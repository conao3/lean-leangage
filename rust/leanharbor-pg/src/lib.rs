//! An engine that stores each tenant's snapshot in PostgreSQL, as `Leanharbor.Storage.Stored`
//! describes. It is trusted: no theorem covers this file.
//!
//! At start it creates the kernel's tables with the statements of the generated `create` and
//! `render`. Each command runs in one `SERIALIZABLE` transaction: it reads the tenant's version,
//! takes the snapshot it remembers for that version or else reads the tenant's rows with the
//! generated `select` of every table and builds the snapshot with the kernel's `load`, calls
//! `transition`, and sends the statements the generated `compile` makes of the generated `plan`
//! of each write. The only other statements are the constant ones of this file: the transaction
//! control, the advisory locks, and the framework's tables `leanharbor_idempotency` and
//! `leanharbor_version`.
//!
//! The contract (the engine's side of `Storage.Stored`):
//!
//! 1. One attempt reads one tenant, calls `transition`, writes and commits in one `SERIALIZABLE`
//!    transaction.
//! 2. A retry opens a new transaction, reads the rows again and calls `transition` again. An
//!    attempt is retried after a lost connection, SQLSTATE 40001, 40P01, 57P01, 57P02 or 53200
//!    from a full table of serializable conflicts, and, with an idempotency key, 23505 and a lost
//!    COMMIT; at most [`Config::max_attempts`] attempts, 20 by default.
//! 3. A refused command rolls back and writes no row.
//! 4. The app's writes and the reply stored under an idempotency key commit in one transaction.
//! 5. The tenant's advisory lock is taken before `BEGIN` and released before the connection
//!    returns to the pool; a connection that fails to release it is closed.
//! 6. A command `read_only` accepts runs in a `SERIALIZABLE READ ONLY DEFERRABLE` transaction,
//!    without the advisory lock and without an idempotency key (a keyed request takes the write
//!    path), and fails if its write set stores a row.
//! 7. A request without an idempotency key whose connection is lost during COMMIT, or whose
//!    COMMIT fails with 57P01 or 57P02, fails with [`EngineError::CommitUnknown`].
//! 8. A transaction whose write set stores a row advances the tenant's row of
//!    `leanharbor_version` by one (from 0 when it has none). An attempt reads that row first and
//!    runs the command on the snapshot the engine remembers for the tenant at that version, or,
//!    when it remembers none, on the snapshot `load` builds of the rows it reads. After a commit
//!    the engine remembers the snapshot `apply` computed, at the version the transaction left;
//!    after a refusal, and on the read-only path, the snapshot the command ran on; after any
//!    other end of the attempt, a COMMIT of unknown outcome included, nothing for the tenant.
//!    It remembers at most [`Config::cache_tenants`] tenants and forgets the one it used least
//!    recently.
//!
//! Every request runs in a task of its own, so a caller that stops waiting (a closed HTTP
//! connection) does not interrupt an attempt between its lock and its unlock.

use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use bytes::BytesMut;
use deadpool_postgres::{Manager, ManagerConfig, Object, Pool, RecyclingMethod};
use leanfran::runtime::Nat;
use leanharbor::sql::{self, Tab, Val};
use leanharbor::{Engine, EngineError, Executed, Idempotency, Kernel, Storage};
use tokio_postgres::error::SqlState;
use tokio_postgres::types::{IsNull, ToSql, Type, to_sql_checked};
use tokio_postgres::{IsolationLevel, NoTls, Row};

pub mod testing;

/// The replies of the commands run under an idempotency key, per tenant, scope and key.
const FRAMEWORK_DDL: &str = "CREATE TABLE IF NOT EXISTS leanharbor_idempotency (\
    tenant_id BIGINT NOT NULL, scope TEXT NOT NULL, key TEXT NOT NULL, \
    fingerprint BYTEA NOT NULL, reply BYTEA NOT NULL, PRIMARY KEY (tenant_id, scope, key))";
/// Each tenant's version: a transaction that writes the tenant's rows advances it by one.
const VERSION_DDL: &str = "CREATE TABLE IF NOT EXISTS leanharbor_version (\
    tenant_id BIGINT PRIMARY KEY, version BIGINT NOT NULL)";
const FRAMEWORK_TABLES: &[&str] = &["leanharbor_idempotency", "leanharbor_version"];
/// The tenant's version; no row is version 0.
const VERSION: &str = "SELECT version FROM leanharbor_version WHERE tenant_id = $1";
const ADVANCE: &str = "INSERT INTO leanharbor_version (tenant_id, version) VALUES ($1, 1) \
    ON CONFLICT (tenant_id) DO UPDATE SET version = leanharbor_version.version + 1 \
    RETURNING version";
const STORED_REPLY: &str = "SELECT fingerprint, reply FROM leanharbor_idempotency \
    WHERE tenant_id = $1 AND scope = $2 AND key = $3";
const STORE_REPLY: &str = "INSERT INTO leanharbor_idempotency \
    (tenant_id, scope, key, fingerprint, reply) VALUES ($1, $2, $3, $4, $5)";
/// Held while the tables are created, so that engines starting together do not race in
/// `CREATE TABLE`. The two-key form, whose keys never meet a tenant's lock.
const SCHEMA_LOCK: &str = "SELECT pg_advisory_lock(1819173234, 0)";
const SCHEMA_UNLOCK: &str = "SELECT pg_advisory_unlock(1819173234, 0)";
/// The tenant's lock: the tenant id as a `BIGINT`.
const TENANT_LOCK: &str = "SELECT pg_advisory_lock($1)";
const UNLOCK_ALL: &str = "SELECT pg_advisory_unlock_all()";
const BACKEND_PID: &str = "SELECT pg_backend_pid()";
const TX_INFO: &str = "SELECT pg_backend_pid(), current_setting('transaction_isolation'), \
    current_setting('transaction_read_only'), current_setting('transaction_deferrable'), \
    (SELECT virtualxid FROM pg_locks WHERE locktype = 'virtualxid' AND pid = pg_backend_pid())";

/// A point of an attempt where [`Config::hook`] is called.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Point {
    /// Before `BEGIN`, holding the tenant's advisory lock if [`Config::tenant_lock`]. Not on the
    /// read-only path.
    Locked,
    /// The version is read, and the rows unless the engine remembers the snapshot of that
    /// version; `transition` has not run.
    Loaded,
    /// The writes and the stored reply are sent, `COMMIT` is not. Not on the read-only path.
    Written,
}

/// The transaction of an attempt, as PostgreSQL reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TxInfo {
    pub vxid: String,
    pub isolation: String,
    pub read_only: bool,
    pub deferrable: bool,
}

/// Where an attempt is when [`Config::hook`] is called.
#[derive(Clone, Debug)]
pub struct Attempt {
    pub point: Point,
    pub tenant: u64,
    /// The process of the attempt's connection.
    pub pid: i32,
    /// From [`Point::Loaded`] on.
    pub tx: Option<TxInfo>,
}

/// Called at each [`Point`] of each attempt; the attempt waits for the future. For tests that
/// inject faults.
pub type Hook = Arc<dyn Fn(Attempt) -> Pin<Box<dyn Future<Output = ()> + Send>> + Send + Sync>;

#[derive(Clone)]
pub struct Config {
    /// Attempts of one command before [`EngineError::RetriesExhausted`].
    pub max_attempts: u32,
    /// Take the tenant's advisory lock before each write attempt. It spares retries;
    /// `SERIALIZABLE` keeps the commits serial without it.
    pub tenant_lock: bool,
    /// Tenants whose snapshot the engine remembers at once; 0 remembers none.
    pub cache_tenants: usize,
    pub hook: Option<Hook>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_attempts: 20,
            tenant_lock: true,
            cache_tenants: 1024,
            hook: None,
        }
    }
}

/// What the engine did, counted since it started.
#[derive(Default, Debug)]
pub struct Stats {
    pub attempts: AtomicU64,
    pub retries: AtomicU64,
    /// Accepted commands committed, on both paths.
    pub commits: AtomicU64,
    /// Requests answered with a stored reply.
    pub replays: AtomicU64,
    /// Attempts on the read-only path, also counted in `attempts`.
    pub reads: AtomicU64,
    /// Attempts that read the tenant's rows: the engine remembered no snapshot at the version
    /// they read.
    pub loads: AtomicU64,
}

/// Why an attempt ended without a decision to return.
enum Failure {
    /// The attempt did not commit.
    Postgres(tokio_postgres::Error),
    /// No connection: the attempt did not start.
    Pool(String),
    /// The connection was lost during COMMIT.
    CommitLost,
    /// Retrying cannot help.
    Final(EngineError),
}

impl From<tokio_postgres::Error> for Failure {
    fn from(e: tokio_postgres::Error) -> Self {
        Failure::Postgres(e)
    }
}

fn broken(message: &str) -> Failure {
    Failure::Final(EngineError::Broken(message.to_owned()))
}

/// SERIALIZABLE ran out of its shared memory for conflicts; PostgreSQL aborted the transaction.
fn ssi_exhausted(e: &tokio_postgres::Error) -> bool {
    e.as_db_error().is_some_and(|db| {
        *db.code() == SqlState::OUT_OF_MEMORY
            && (db.message().contains("RWConflictPool")
                || db
                    .hint()
                    .is_some_and(|h| h.contains("max_pred_locks_per_transaction")))
    })
}

impl Failure {
    fn retryable(&self, keyed: bool) -> bool {
        match self {
            Failure::Pool(_) => true,
            Failure::Postgres(e) => {
                e.is_closed()
                    || ssi_exhausted(e)
                    || e.code().is_some_and(|c| {
                        *c == SqlState::T_R_SERIALIZATION_FAILURE
                            || *c == SqlState::T_R_DEADLOCK_DETECTED
                            || *c == SqlState::ADMIN_SHUTDOWN
                            || *c == SqlState::CRASH_SHUTDOWN
                            || (keyed && *c == SqlState::UNIQUE_VIOLATION)
                    })
            }
            Failure::CommitLost => keyed,
            Failure::Final(_) => false,
        }
    }

    fn into_error(self) -> EngineError {
        match self {
            Failure::Postgres(e) => EngineError::Database(e.to_string()),
            Failure::Pool(e) => EngineError::Database(e),
            Failure::CommitLost => EngineError::CommitUnknown,
            Failure::Final(e) => e,
        }
    }
}

/// A COMMIT that failed without a server's error code, or because the server ended the
/// connection, may have committed.
fn commit_failure(e: tokio_postgres::Error) -> Failure {
    match e.code() {
        None => Failure::CommitLost,
        Some(c) if *c == SqlState::ADMIN_SHUTDOWN || *c == SqlState::CRASH_SHUTDOWN => {
            Failure::CommitLost
        }
        Some(_) => Failure::Postgres(e),
    }
}

/// A value as a parameter of the type PostgreSQL inferred for it.
struct Param<'a>(&'a Val);

impl std::fmt::Debug for Param<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl ToSql for Param<'_> {
    fn to_sql(
        &self,
        ty: &Type,
        out: &mut BytesMut,
    ) -> Result<IsNull, Box<dyn std::error::Error + Sync + Send>> {
        match self.0 {
            Val::Int { v } if *ty == Type::INT8 => v.to_sql(ty, out),
            Val::Bool { v } if *ty == Type::BOOL => v.to_sql(ty, out),
            Val::Text { v } if *ty == Type::TEXT => v.to_sql(ty, out),
            Val::Bytes { v } if *ty == Type::BYTEA => v.as_slice().to_sql(ty, out),
            Val::Null => Ok(IsNull::Yes),
            other => Err(format!("{other:?} as a parameter of type {ty}").into()),
        }
    }

    fn accepts(_: &Type) -> bool {
        true
    }

    to_sql_checked!();
}

fn params(ps: &[Val]) -> Vec<Param<'_>> {
    ps.iter().map(Param).collect()
}

fn refs<'a>(ps: &'a [Param<'a>]) -> Vec<&'a (dyn ToSql + Sync)> {
    ps.iter().map(|p| p as &(dyn ToSql + Sync)).collect()
}

/// A row as values, by the type of each column.
fn values(row: &Row) -> Result<Vec<Val>, Failure> {
    let mut vals = Vec::with_capacity(row.len());
    for (i, column) in row.columns().iter().enumerate() {
        let ty = column.type_();
        let val = if *ty == Type::INT8 {
            row.try_get::<_, Option<i64>>(i)?.map(|v| Val::Int { v })
        } else if *ty == Type::BOOL {
            row.try_get::<_, Option<bool>>(i)?.map(|v| Val::Bool { v })
        } else if *ty == Type::TEXT {
            row.try_get::<_, Option<String>>(i)?
                .map(|v| Val::Text { v })
        } else if *ty == Type::BYTEA {
            row.try_get::<_, Option<Vec<u8>>>(i)?
                .map(|v| Val::Bytes { v })
        } else {
            return Err(broken(&format!("a column of type {ty}")));
        };
        vals.push(val.unwrap_or(Val::Null));
    }
    Ok(vals)
}

/// What `transition` decided, with the snapshot to remember if the attempt ends as it should:
/// the one the command ran on after a refusal, the one `apply` computed after an acceptance.
enum Decided<K: Kernel> {
    Refused {
        snap: K::Snapshot,
        error: K::Error,
    },
    Accepted {
        snap: K::Snapshot,
        statements: Vec<(String, Vec<Val>)>,
        reply: K::Reply,
    },
}

/// Runs the command on the snapshot, applies the writes of an accepted command to it and
/// compiles them. A view of Lean's stays in this function, which does not wait: it may stay on
/// one thread.
fn decide<K: Storage>(
    tables: &[Tab],
    tv: i64,
    mut snap: K::Snapshot,
    actor: &K::Principal,
    cmd: &K::Command,
) -> Result<Decided<K>, Failure> {
    let decision = K::lend(&mut snap, |view| match K::transition(actor, &view, cmd) {
        Ok((ws, reply)) => {
            let writes = K::writes(&ws);
            (K::apply(view, ws), Ok((writes, reply)))
        }
        Err(e) => (view, Err(e)),
    });
    let (writes, reply) = match decision {
        Ok(accepted) => accepted,
        Err(error) => return Ok(Decided::Refused { snap, error }),
    };
    let mut statements = Vec::new();
    for write in writes {
        let (q, ps) = sql::compile(tables.to_vec(), tv, sql::plan(write))
            .ok_or_else(|| broken("a write does not compile"))?;
        statements.push((sql::render(q), ps));
    }
    Ok(Decided::Accepted {
        snap,
        statements,
        reply,
    })
}

/// A snapshot the engine remembers, with the tenant's version it stands for.
struct Remembered<S> {
    version: i64,
    snap: S,
    used: u64,
}

/// The snapshots the engine remembers, at most `capacity` tenants.
struct Cache<S> {
    capacity: usize,
    clock: u64,
    tenants: HashMap<u64, Remembered<S>>,
}

impl<S> Cache<S> {
    /// The snapshot of the tenant at `version`, which the cache no longer holds. A snapshot of
    /// an earlier version is forgotten.
    fn take(&mut self, tenant: u64, version: i64) -> Option<S> {
        let found = self.tenants.get(&tenant)?.version;
        if found > version {
            return None;
        }
        let entry = self.tenants.remove(&tenant)?;
        (found == version).then_some(entry.snap)
    }

    /// Remembers the snapshot of the tenant at `version`, unless it holds one of a later
    /// version, and forgets the tenant used least recently beyond the capacity.
    fn put(&mut self, tenant: u64, version: i64, snap: S) {
        if self.capacity == 0
            || self
                .tenants
                .get(&tenant)
                .is_some_and(|e| e.version > version)
        {
            return;
        }
        self.clock += 1;
        let used = self.clock;
        self.tenants.insert(
            tenant,
            Remembered {
                version,
                snap,
                used,
            },
        );
        if self.tenants.len() > self.capacity {
            let oldest = self
                .tenants
                .iter()
                .min_by_key(|(_, e)| e.used)
                .map(|(t, _)| *t);
            if let Some(t) = oldest {
                self.tenants.remove(&t);
            }
        }
    }
}

fn backoff(attempt: u32) -> Duration {
    let cap_us = 1000u64 << attempt.min(8);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.subsec_nanos());
    Duration::from_micros(u64::from(nanos) % cap_us + 100)
}

fn database(e: impl std::fmt::Display) -> EngineError {
    EngineError::Database(e.to_string())
}

struct Inner<K: Kernel> {
    pool: Pool,
    tables: Vec<Tab>,
    config: Config,
    stats: Stats,
    cache: Mutex<Cache<K::Snapshot>>,
}

/// The engine: a pool of connections to one database, and the snapshots it remembers.
pub struct PgEngine<K: Kernel> {
    inner: Arc<Inner<K>>,
}

impl<K: Storage> PgEngine<K> {
    /// Opens a pool of up to `size` connections to `url` and creates the tables that do not
    /// exist, with the generated `create` of each of `K::tables()` and the framework's tables.
    pub async fn connect(url: &str, size: usize, config: Config) -> Result<Self, EngineError> {
        let tables = K::tables();
        if !sql::valid(tables.clone()) {
            return Err(EngineError::Broken("the tables are not valid".to_owned()));
        }
        let pg: tokio_postgres::Config = url.parse().map_err(database)?;
        let (client, connection) = pg.connect(NoTls).await.map_err(database)?;
        let task = tokio::spawn(connection);
        let created = create(&client, &tables).await;
        drop(client);
        let _ = task.await;
        created.map_err(database)?;
        let manager = Manager::from_config(
            pg,
            NoTls,
            ManagerConfig {
                recycling_method: RecyclingMethod::Fast,
            },
        );
        let pool = Pool::builder(manager)
            .max_size(size)
            .build()
            .map_err(database)?;
        let cache = Mutex::new(Cache {
            capacity: config.cache_tenants,
            clock: 0,
            tenants: HashMap::new(),
        });
        Ok(PgEngine {
            inner: Arc::new(Inner {
                pool,
                tables,
                config,
                stats: Stats::default(),
                cache,
            }),
        })
    }

    pub fn stats(&self) -> &Stats {
        &self.inner.stats
    }

    /// Connections open and idle in the pool.
    pub fn idle(&self) -> usize {
        self.inner.pool.status().available
    }

    /// Tenants whose snapshot the engine remembers.
    pub fn cached(&self) -> usize {
        self.inner.cache.lock().map_or(0, |c| c.tenants.len())
    }
}

async fn create(
    client: &tokio_postgres::Client,
    tables: &[Tab],
) -> Result<(), tokio_postgres::Error> {
    client.batch_execute(SCHEMA_LOCK).await?;
    let created = async {
        client.execute(FRAMEWORK_DDL, &[]).await?;
        client.execute(VERSION_DDL, &[]).await?;
        for t in tables {
            client
                .execute(&sql::render(sql::create(t.clone())), &[])
                .await?;
        }
        Ok(())
    }
    .await;
    client.batch_execute(SCHEMA_UNLOCK).await?;
    created
}

impl<K: Storage> Inner<K> {
    async fn fire_locked(&self, client: &Object, tenant: u64) -> Result<(), Failure> {
        let Some(hook) = &self.config.hook else {
            return Ok(());
        };
        let pid: i32 = client.query_one(BACKEND_PID, &[]).await?.get(0);
        hook(Attempt {
            point: Point::Locked,
            tenant,
            pid,
            tx: None,
        })
        .await;
        Ok(())
    }

    async fn fire(
        &self,
        tx: &deadpool_postgres::Transaction<'_>,
        point: Point,
        tenant: u64,
    ) -> Result<(), Failure> {
        let Some(hook) = &self.config.hook else {
            return Ok(());
        };
        let row = tx.query_one(TX_INFO, &[]).await?;
        let info = TxInfo {
            isolation: row.get(1),
            read_only: row.get::<_, String>(2) == "on",
            deferrable: row.get::<_, String>(3) == "on",
            vxid: row.get(4),
        };
        hook(Attempt {
            point,
            tenant,
            pid: row.get(0),
            tx: Some(info),
        })
        .await;
        Ok(())
    }

    /// The tenant's version, and the snapshot remembered for it or else the one `load` builds of
    /// the rows of every table for the tenant, read by the generated `select`.
    async fn snapshot(
        &self,
        tx: &deadpool_postgres::Transaction<'_>,
        tenant: u64,
        tv: i64,
    ) -> Result<(i64, K::Snapshot), Failure> {
        let st = tx.prepare_cached(VERSION).await?;
        let version = match tx.query_opt(&st, &[&tv]).await? {
            Some(row) => row.try_get(0)?,
            None => 0,
        };
        let remembered = self
            .cache
            .lock()
            .ok()
            .and_then(|mut c| c.take(tenant, version));
        if let Some(snap) = remembered {
            return Ok((version, snap));
        }
        self.stats.loads.fetch_add(1, Ordering::Relaxed);
        let rows = self.load(tx, tv).await?;
        let snap = K::load(rows).ok_or_else(|| broken("the stored rows do not load"))?;
        Ok((version, snap))
    }

    fn remember(&self, tenant: u64, version: i64, snap: K::Snapshot) {
        if let Ok(mut c) = self.cache.lock() {
            c.put(tenant, version, snap);
        }
    }

    /// The rows of every table for the tenant, by the generated `select`.
    async fn load(
        &self,
        tx: &deadpool_postgres::Transaction<'_>,
        tv: i64,
    ) -> Result<Vec<Vec<Vec<Val>>>, Failure> {
        let mut all = Vec::with_capacity(self.tables.len());
        for t in 0..self.tables.len() {
            let (q, ps) = sql::select(self.tables.clone(), tv, Nat::from(t), None)
                .ok_or_else(|| broken("a table has no SELECT"))?;
            let st = tx.prepare_cached(&sql::render(q)).await?;
            let ps = params(&ps);
            let rows = tx.query(&st, &refs(&ps)).await?;
            all.push(rows.iter().map(values).collect::<Result<Vec<_>, _>>()?);
        }
        Ok(all)
    }

    async fn run(
        &self,
        actor: K::Principal,
        cmd: K::Command,
        idem: Option<Idempotency>,
    ) -> Executed<K> {
        let read = idem.is_none() && K::read_only(&cmd);
        let keyed = idem.is_some();
        for attempt in 0..self.config.max_attempts {
            self.stats.attempts.fetch_add(1, Ordering::Relaxed);
            let result = if read {
                self.stats.reads.fetch_add(1, Ordering::Relaxed);
                self.read_attempt(&actor, &cmd).await
            } else {
                self.write_attempt(&actor, &cmd, idem.as_ref()).await
            };
            match result {
                Ok(decided) => return Ok(decided),
                Err(f) if f.retryable(keyed) => {
                    self.stats.retries.fetch_add(1, Ordering::Relaxed);
                    tokio::time::sleep(backoff(attempt)).await;
                }
                Err(f) => return Err(f.into_error()),
            }
        }
        Err(EngineError::RetriesExhausted)
    }

    /// One attempt on a connection of its own, returned to the pool only when it ended
    /// without a failure and holds no advisory lock.
    async fn write_attempt(
        &self,
        actor: &K::Principal,
        cmd: &K::Command,
        idem: Option<&Idempotency>,
    ) -> Result<Result<K::Reply, K::Error>, Failure> {
        let tenant = K::tenant(actor);
        let tv = tenant as i64;
        let mut client = self
            .pool
            .get()
            .await
            .map_err(|e| Failure::Pool(e.to_string()))?;
        let mut result = Ok(());
        if self.config.tenant_lock {
            result = client
                .execute(TENANT_LOCK, &[&tv])
                .await
                .map(|_| ())
                .map_err(Failure::from);
        }
        let result = match result {
            Ok(()) => match self.fire_locked(&client, tenant).await {
                Ok(()) => self.transact(&mut client, actor, cmd, idem, tv).await,
                Err(f) => Err(f),
            },
            Err(f) => Err(f),
        };
        let unlocked = !self.config.tenant_lock || client.execute(UNLOCK_ALL, &[]).await.is_ok();
        if result.is_err() || !unlocked {
            drop(Object::take(client));
        }
        result
    }

    async fn transact(
        &self,
        client: &mut Object,
        actor: &K::Principal,
        cmd: &K::Command,
        idem: Option<&Idempotency>,
        tv: i64,
    ) -> Result<Result<K::Reply, K::Error>, Failure> {
        let tenant = K::tenant(actor);
        let tx = client
            .build_transaction()
            .isolation_level(IsolationLevel::Serializable)
            .start()
            .await?;
        if let Some(idem) = idem {
            let st = tx.prepare_cached(STORED_REPLY).await?;
            if let Some(row) = tx.query_opt(&st, &[&tv, &idem.scope, &idem.key]).await? {
                let fingerprint: Vec<u8> = row.try_get(0)?;
                if fingerprint != idem.fingerprint {
                    tx.rollback().await?;
                    return Err(Failure::Final(EngineError::IdempotencyConflict));
                }
                let bytes: Vec<u8> = row.try_get(1)?;
                let reply = K::decode_reply(&bytes)
                    .ok_or_else(|| broken("a stored reply does not decode"))?;
                tx.rollback().await?;
                self.stats.replays.fetch_add(1, Ordering::Relaxed);
                return Ok(Ok(reply));
            }
        }
        let (version, snap) = self.snapshot(&tx, tenant, tv).await?;
        self.fire(&tx, Point::Loaded, tenant).await?;
        let (snap, statements, reply) = match decide::<K>(&self.tables, tv, snap, actor, cmd)? {
            Decided::Refused { snap, error } => {
                self.remember(tenant, version, snap);
                tx.rollback().await?;
                return Ok(Err(error));
            }
            Decided::Accepted {
                snap,
                statements,
                reply,
            } => (snap, statements, reply),
        };
        for (text, ps) in &statements {
            let st = tx.prepare_cached(text).await?;
            let ps = params(ps);
            tx.execute(&st, &refs(&ps)).await?;
        }
        let version = if statements.is_empty() {
            version
        } else {
            let st = tx.prepare_cached(ADVANCE).await?;
            tx.query_one(&st, &[&tv]).await?.try_get(0)?
        };
        if let Some(idem) = idem {
            let st = tx.prepare_cached(STORE_REPLY).await?;
            let bytes = K::encode_reply(&reply);
            tx.execute(
                &st,
                &[&tv, &idem.scope, &idem.key, &idem.fingerprint, &bytes],
            )
            .await?;
        }
        self.fire(&tx, Point::Written, tenant).await?;
        tx.commit().await.map_err(commit_failure)?;
        self.remember(tenant, version, snap);
        self.stats.commits.fetch_add(1, Ordering::Relaxed);
        Ok(Ok(reply))
    }

    async fn read_attempt(
        &self,
        actor: &K::Principal,
        cmd: &K::Command,
    ) -> Result<Result<K::Reply, K::Error>, Failure> {
        let tenant = K::tenant(actor);
        let tv = tenant as i64;
        let mut client = self
            .pool
            .get()
            .await
            .map_err(|e| Failure::Pool(e.to_string()))?;
        let result = self.read_transact(&mut client, actor, cmd, tv).await;
        if result.is_err() {
            drop(Object::take(client));
        }
        result
    }

    async fn read_transact(
        &self,
        client: &mut Object,
        actor: &K::Principal,
        cmd: &K::Command,
        tv: i64,
    ) -> Result<Result<K::Reply, K::Error>, Failure> {
        let tx = client
            .build_transaction()
            .isolation_level(IsolationLevel::Serializable)
            .read_only(true)
            .deferrable(true)
            .start()
            .await?;
        let tenant = K::tenant(actor);
        let (version, snap) = self.snapshot(&tx, tenant, tv).await?;
        self.fire(&tx, Point::Loaded, tenant).await?;
        match decide::<K>(&self.tables, tv, snap, actor, cmd)? {
            Decided::Refused { snap, error } => {
                self.remember(tenant, version, snap);
                tx.rollback().await?;
                Ok(Err(error))
            }
            Decided::Accepted {
                snap,
                statements,
                reply,
            } => {
                if !statements.is_empty() {
                    tx.rollback().await?;
                    return Err(broken("a read-only command wrote"));
                }
                self.remember(tenant, version, snap);
                tx.commit().await?;
                self.stats.commits.fetch_add(1, Ordering::Relaxed);
                Ok(Ok(reply))
            }
        }
    }
}

impl<K: Storage> Engine<K> for PgEngine<K>
where
    K::Principal: Sync,
    K::Command: Sync,
{
    async fn execute(
        &self,
        actor: K::Principal,
        cmd: K::Command,
        idempotency: Option<Idempotency>,
    ) -> Executed<K> {
        let inner = self.inner.clone();
        let task = tokio::spawn(async move { inner.run(actor, cmd, idempotency).await });
        task.await
            .unwrap_or_else(|e| Err(EngineError::Broken(format!("the request failed: {e}"))))
    }
}

fn role(name: &str) -> Result<&str, EngineError> {
    let mut chars = name.chars();
    let first = chars
        .next()
        .is_some_and(|c| c.is_ascii_lowercase() || c == '_');
    if first
        && name.len() <= 63
        && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
    {
        Ok(name)
    } else {
        Err(EngineError::Broken(format!(
            "the role name {name:?} is not [a-z_][a-z0-9_]*"
        )))
    }
}

/// Run by an administrator of the database: creates the tables of `K` and the framework's
/// tables, makes `owner` own them, and lets `engine_role` read and write their rows and nothing
/// else: it cannot alter, drop or truncate them. `owner` is created without the right to log
/// in if it does not exist. `engine_role` must exist and may not be a superuser; it gets
/// `USAGE` and `CREATE` on the schema, so that the engine's `CREATE TABLE IF NOT EXISTS` at start
/// finds the tables.
pub async fn lockdown<K: Storage>(
    admin_url: &str,
    owner: &str,
    engine_role: &str,
) -> Result<(), EngineError> {
    let (owner, engine) = (role(owner)?, role(engine_role)?);
    if owner == engine {
        return Err(EngineError::Broken(
            "the owner and the engine's role must differ".to_owned(),
        ));
    }
    let tables = K::tables();
    if !sql::valid(tables.clone()) {
        return Err(EngineError::Broken("the tables are not valid".to_owned()));
    }
    let (admin, connection) = tokio_postgres::connect(admin_url, NoTls)
        .await
        .map_err(database)?;
    let task = tokio::spawn(connection);
    let result: Result<Result<(), String>, tokio_postgres::Error> = async {
        let engine_row = admin
            .query_opt(
                "SELECT rolsuper FROM pg_roles WHERE rolname = $1",
                &[&engine],
            )
            .await?;
        match engine_row.map(|r| r.get::<_, bool>(0)) {
            None => return Ok(Err(format!("the role {engine} does not exist"))),
            Some(true) => return Ok(Err(format!("the role {engine} is a superuser"))),
            Some(false) => {}
        }
        admin
            .batch_execute(&format!(
                "DO $$ BEGIN IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = '{owner}') \
                 THEN CREATE ROLE \"{owner}\" NOLOGIN; END IF; END $$"
            ))
            .await?;
        let login: bool = admin
            .query_one(
                "SELECT rolcanlogin FROM pg_roles WHERE rolname = $1",
                &[&owner],
            )
            .await?
            .get(0);
        if login {
            return Ok(Err(format!("the role {owner} can log in")));
        }
        create(&admin, &tables).await?;
        let names = FRAMEWORK_TABLES
            .iter()
            .map(|n| (*n).to_owned())
            .chain(tables.iter().map(|t| t.name.clone()));
        for name in names {
            let q = sql::quote(name);
            admin
                .batch_execute(&format!(
                    "ALTER TABLE {q} OWNER TO \"{owner}\"; REVOKE ALL ON {q} FROM PUBLIC; \
                     REVOKE ALL ON {q} FROM \"{engine}\"; \
                     GRANT SELECT, INSERT, UPDATE, DELETE ON {q} TO \"{engine}\""
                ))
                .await?;
        }
        admin
            .batch_execute(&format!(
                "DO $$ BEGIN EXECUTE format('GRANT USAGE, CREATE ON SCHEMA %I TO %I', \
                 current_schema(), '{engine}'); END $$"
            ))
            .await?;
        Ok(Ok(()))
    }
    .await;
    drop(admin);
    let _ = task.await;
    match result {
        Ok(Ok(())) => Ok(()),
        Ok(Err(message)) => Err(EngineError::Broken(message)),
        Err(e) => Err(database(e)),
    }
}
