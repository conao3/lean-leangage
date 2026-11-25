//! A small kernel written in Rust for the engine's tests, a proxy that loses a COMMIT, and the
//! queries a test makes as the server's superuser.

#![allow(dead_code)]

use std::collections::{BTreeMap, VecDeque};
use std::future::Future;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use leanfran::runtime::Nat;
use leanharbor::sql::{Col, Kind, Tab, Val, Write};
use leanharbor::{Kernel, Storage};
use leanharbor_pg::testing::{Cluster, cluster, connect};
use leanharbor_pg::{Attempt, Config, Hook, PgEngine};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

/// Numbered cells of integers per tenant. `Poke` claims to read only and writes.
pub struct Cells;

#[derive(Clone, Debug)]
pub struct Actor {
    pub tenant: u64,
    pub user: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cmd {
    Add { cell: i64, delta: i64 },
    Move { from: i64, to: i64, amount: i64 },
    Get { cell: i64 },
    Poke { cell: i64 },
}

#[derive(Debug, PartialEq, Eq)]
pub enum Refused {
    Negative,
}

impl Kernel for Cells {
    type Principal = Actor;
    type Snapshot = BTreeMap<i64, i64>;
    type View = BTreeMap<i64, i64>;
    type Command = Cmd;
    type WriteSet = Vec<(i64, i64)>;
    type Reply = i64;
    type Error = Refused;

    fn init() -> Self::Snapshot {
        BTreeMap::new()
    }

    fn tenant(actor: &Actor) -> u64 {
        actor.tenant
    }

    fn lend<R>(snap: &mut Self::Snapshot, f: impl FnOnce(Self::View) -> (Self::View, R)) -> R {
        let (view, r) = f(std::mem::take(snap));
        *snap = view;
        r
    }

    fn transition(
        _: &Actor,
        snap: &Self::View,
        cmd: &Cmd,
    ) -> Result<(Vec<(i64, i64)>, i64), Refused> {
        let get = |c: &i64| snap.get(c).copied().unwrap_or(0);
        match cmd {
            Cmd::Add { cell, delta } => {
                let v = get(cell) + delta;
                if v < 0 {
                    return Err(Refused::Negative);
                }
                Ok((vec![(*cell, v)], v))
            }
            Cmd::Move { from, to, amount } => {
                let f = get(from) - amount;
                if f < 0 {
                    return Err(Refused::Negative);
                }
                Ok((vec![(*from, f), (*to, get(to) + amount)], f))
            }
            Cmd::Get { cell } => Ok((vec![], get(cell))),
            Cmd::Poke { cell } => Ok((vec![(*cell, get(cell) + 1)], get(cell) + 1)),
        }
    }

    fn apply(mut snap: Self::View, ws: Vec<(i64, i64)>) -> Self::View {
        snap.extend(ws);
        snap
    }

    fn read_only(cmd: &Cmd) -> bool {
        matches!(cmd, Cmd::Get { .. } | Cmd::Poke { .. })
    }
}

fn col(name: &str, kind: Kind, nullable: bool) -> Col {
    Col {
        name: name.to_owned(),
        kind,
        nullable,
    }
}

impl Storage for Cells {
    fn tables() -> Vec<Tab> {
        vec![Tab {
            name: "cells".to_owned(),
            cols: vec![col("id", Kind::Int, false), col("v", Kind::Int, false)],
            kl: Nat::from(1_u64),
        }]
    }

    fn load(rows: Vec<Vec<Vec<Val>>>) -> Option<Self::Snapshot> {
        let [rows] = <[_; 1]>::try_from(rows).ok()?;
        rows.into_iter()
            .map(|row| match row.as_slice() {
                [Val::Int { v: id }, Val::Int { v }] => Some((*id, *v)),
                _ => None,
            })
            .collect()
    }

    fn writes(ws: &Vec<(i64, i64)>) -> Vec<Write> {
        ws.iter()
            .map(|&(id, v)| Write::Put {
                table: Nat::from(0_u64),
                key_len: Nat::from(1_u64),
                row: vec![Val::Int { v: id }, Val::Int { v }],
            })
            .collect()
    }

    fn encode_reply(reply: &i64) -> Vec<u8> {
        reply.to_be_bytes().to_vec()
    }

    fn decode_reply(bytes: &[u8]) -> Option<i64> {
        Some(i64::from_be_bytes(bytes.try_into().ok()?))
    }
}

pub fn add(cell: i64, delta: i64) -> Cmd {
    Cmd::Add { cell, delta }
}

pub fn actor(tenant: u64) -> Actor {
    Actor { tenant, user: 1 }
}

/// One database of the test process's server, with the tables of `Cells` made by `lockdown`.
pub struct Db {
    pub name: String,
    /// The engine role's connection string.
    pub url: String,
    pub admin: Arc<tokio_postgres::Client>,
}

pub async fn setup(name: &str) -> Db {
    let url = cluster().locked::<Cells>(name).await;
    let admin = Arc::new(connect(&cluster().admin_url(name)).await);
    Db {
        name: name.to_owned(),
        url,
        admin,
    }
}

impl Db {
    pub async fn engine(&self, size: usize, config: Config) -> PgEngine<Cells> {
        self.engine_at(&self.url, size, config).await
    }

    pub async fn engine_at(&self, url: &str, size: usize, config: Config) -> PgEngine<Cells> {
        PgEngine::connect(url, size, config)
            .await
            .expect("the engine connects")
    }

    pub fn admin_url(&self) -> String {
        cluster().admin_url(&self.name)
    }

    pub async fn cells(&self, tenant: u64) -> BTreeMap<i64, i64> {
        self.admin
            .query(
                "SELECT id, v FROM cells WHERE tenant_id = $1",
                &[&(tenant as i64)],
            )
            .await
            .unwrap()
            .iter()
            .map(|r| (r.get(0), r.get(1)))
            .collect()
    }

    pub async fn cell(&self, tenant: u64, id: i64) -> Option<i64> {
        self.cells(tenant).await.get(&id).copied()
    }

    pub async fn replies(&self, tenant: u64) -> i64 {
        self.admin
            .query_one(
                "SELECT count(*) FROM leanharbor_idempotency WHERE tenant_id = $1",
                &[&(tenant as i64)],
            )
            .await
            .unwrap()
            .get(0)
    }

    /// Advisory locks in this database held or awaited by any session but this one.
    pub async fn advisory_locks(&self) -> i64 {
        self.admin
            .query_one(
                "SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND pid <> pg_backend_pid() \
                 AND database = (SELECT oid FROM pg_database WHERE datname = current_database())",
                &[],
            )
            .await
            .unwrap()
            .get(0)
    }

    pub async fn advisory_locks_of(&self, pid: i32) -> i64 {
        self.admin
            .query_one(
                "SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND pid = $1",
                &[&pid],
            )
            .await
            .unwrap()
            .get(0)
    }

    /// Waits until no session but this one holds an advisory lock; the number left.
    pub async fn no_advisory_locks(&self, within: Duration) -> i64 {
        let start = std::time::Instant::now();
        loop {
            let n = self.advisory_locks().await;
            if n == 0 || start.elapsed() > within {
                return n;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
}

/// Terminates the backend and waits until it is gone.
pub async fn kill(admin: &tokio_postgres::Client, pid: i32) {
    let ok: bool = admin
        .query_one("SELECT pg_terminate_backend($1)", &[&pid])
        .await
        .unwrap()
        .get(0);
    assert!(ok, "backend {pid} terminated");
    for _ in 0..500 {
        let n: i64 = admin
            .query_one(
                "SELECT count(*) FROM pg_stat_activity WHERE pid = $1",
                &[&pid],
            )
            .await
            .unwrap()
            .get(0);
        if n == 0 {
            return;
        }
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    panic!("backend {pid} still runs");
}

/// A hook that runs `f` at `point` for the first `times` attempts that reach it, and records
/// every attempt it sees.
pub struct Recorder {
    pub seen: Mutex<Vec<Attempt>>,
    fired: AtomicU64,
}

pub fn hook_at<F, Fut>(point: leanharbor_pg::Point, times: u64, f: F) -> (Hook, Arc<Recorder>)
where
    F: Fn(Attempt) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = ()> + Send + 'static,
{
    let recorder = Arc::new(Recorder {
        seen: Mutex::new(Vec::new()),
        fired: AtomicU64::new(0),
    });
    let r = recorder.clone();
    let f = Arc::new(f);
    let hook: Hook = Arc::new(
        move |attempt: Attempt| -> Pin<Box<dyn Future<Output = ()> + Send>> {
            r.seen.lock().unwrap().push(attempt.clone());
            let run = attempt.point == point && r.fired.fetch_add(1, Ordering::SeqCst) < times;
            let f = f.clone();
            Box::pin(async move {
                if run {
                    f(attempt).await;
                }
            })
        },
    );
    (hook, recorder)
}

impl Recorder {
    pub fn at(&self, point: leanharbor_pg::Point) -> Vec<Attempt> {
        self.seen
            .lock()
            .unwrap()
            .iter()
            .filter(|a| a.point == point)
            .cloned()
            .collect()
    }
}

pub fn config(max_attempts: u32, tenant_lock: bool, hook: Option<Hook>) -> Config {
    Config {
        max_attempts,
        tenant_lock,
        hook,
        ..Config::default()
    }
}

/// What the proxy does with the next COMMIT it relays.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    /// Close both sides without sending COMMIT: the server rolls back.
    DropBefore,
    /// Send COMMIT, wait for the server's answer, then close both sides without relaying it.
    DropAfter,
}

/// What the server answered a COMMIT the proxy kept from the client.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    NotSent,
    Committed,
    Failed,
}

#[derive(Default)]
struct Plan {
    faults: VecDeque<Fault>,
    outcomes: Vec<Outcome>,
}

/// A TCP proxy in front of the server's Unix socket that can lose the next COMMIT. It reads
/// the frontend protocol (the startup message, then typed messages) and acts on a simple-query
/// `COMMIT`, which is how tokio-postgres commits.
pub struct Proxy {
    pub port: u16,
    plan: Arc<Mutex<Plan>>,
}

impl Proxy {
    pub async fn start(cluster: &Cluster) -> Proxy {
        let socket: PathBuf = cluster.socket();
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let proxy = Proxy {
            port: listener.local_addr().unwrap().port(),
            plan: Arc::default(),
        };
        let plan = proxy.plan.clone();
        tokio::spawn(async move {
            loop {
                let Ok((client, _)) = listener.accept().await else {
                    return;
                };
                let (socket, plan) = (socket.clone(), plan.clone());
                tokio::spawn(async move {
                    if let Ok(server) = tokio::net::UnixStream::connect(&socket).await {
                        relay(client, server, plan).await;
                    }
                });
            }
        });
        proxy
    }

    pub fn arm(&self, f: Fault) {
        self.plan.lock().unwrap().faults.push_back(f);
    }

    pub fn outcomes(&self) -> Vec<Outcome> {
        self.plan.lock().unwrap().outcomes.clone()
    }

    /// The engine role's connection string to `database` through the proxy.
    pub fn url(&self, database: &str) -> String {
        format!(
            "host=127.0.0.1 port={} user={} dbname={database}",
            self.port,
            leanharbor_pg::testing::ENGINE_ROLE
        )
    }
}

/// The next whole message in `buf`: the untyped startup message first, then messages of a type
/// byte, a length and a body.
fn next_message(buf: &mut Vec<u8>, typed: bool) -> Option<Vec<u8>> {
    let (head, len_at) = if typed { (5, 1) } else { (4, 0) };
    if buf.len() < head {
        return None;
    }
    let len = u32::from_be_bytes(buf[len_at..len_at + 4].try_into().unwrap()) as usize;
    let total = len + len_at;
    if buf.len() < total {
        return None;
    }
    Some(buf.drain(..total).collect())
}

async fn relay(
    client: tokio::net::TcpStream,
    server: tokio::net::UnixStream,
    plan: Arc<Mutex<Plan>>,
) {
    let _ = client.set_nodelay(true);
    let (mut cr, mut cw) = client.into_split();
    let (mut sr, mut sw) = server.into_split();
    let (mut from_client, mut from_server) = (Vec::new(), Vec::new());
    let (mut started, mut swallowing, mut committed) = (false, false, false);
    let (mut a, mut b) = (vec![0u8; 16384], vec![0u8; 16384]);
    loop {
        tokio::select! {
            n = cr.read(&mut a) => {
                let Ok(n) = n else { return };
                if n == 0 { return }
                from_client.extend_from_slice(&a[..n]);
                while let Some(m) = next_message(&mut from_client, started) {
                    started = true;
                    if m[0] == b'Q' && &m[5..] == b"COMMIT\0" {
                        let fault = plan.lock().unwrap().faults.pop_front();
                        match fault {
                            Some(Fault::DropBefore) => {
                                plan.lock().unwrap().outcomes.push(Outcome::NotSent);
                                return;
                            }
                            Some(Fault::DropAfter) => swallowing = true,
                            None => {}
                        }
                    }
                    if sw.write_all(&m).await.is_err() { return }
                }
            }
            n = sr.read(&mut b) => {
                let Ok(n) = n else { return };
                if n == 0 { return }
                if !swallowing {
                    if cw.write_all(&b[..n]).await.is_err() { return }
                    continue;
                }
                from_server.extend_from_slice(&b[..n]);
                while let Some(m) = next_message(&mut from_server, true) {
                    // Answers to messages sent before COMMIT may come first. COMMIT ends with
                    // ReadyForQuery `I`: outside a transaction.
                    if m[0] == b'C' && m[5..].starts_with(b"COMMIT") {
                        committed = true;
                    }
                    if m[0] == b'Z' && m.get(5) == Some(&b'I') {
                        let outcome = if committed { Outcome::Committed } else { Outcome::Failed };
                        plan.lock().unwrap().outcomes.push(outcome);
                        return;
                    }
                }
            }
        }
    }
}
