//! The engine's contract, item by item (the numbers of the list in `src/lib.rs`), against the
//! test process's PostgreSQL with injected faults: forced serialization failures and deadlocks,
//! terminated backends, COMMITs lost before or after the server ran them, callers that stop
//! waiting, other engines writing the same tenant, and many concurrent clients. Each test has a
//! database of its own.

mod common;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use common::*;
use leanharbor::{Engine, EngineError, Executed, Idempotency};
use leanharbor_pg::testing::{ENGINE_ROLE, OWNER, cluster, connect};
use leanharbor_pg::{Config, PgEngine, Point, lockdown};
use tokio::sync::Notify;

const T: Duration = Duration::from_secs(30);

/// The outside transaction of `deadlocks_are_retried`.
type Outside = tokio::task::JoinHandle<Result<(), tokio_postgres::Error>>;

fn key(key: &str, cmd: &Cmd) -> Option<Idempotency> {
    Some(Idempotency {
        scope: "u1".to_owned(),
        key: key.to_owned(),
        fingerprint: format!("{cmd:?}").into_bytes(),
    })
}

async fn run(engine: &PgEngine<Cells>, tenant: u64, cmd: Cmd) -> Executed<Cells> {
    tokio::time::timeout(T, engine.execute(actor(tenant), cmd, None))
        .await
        .expect("in time")
}

async fn run_keyed(engine: &PgEngine<Cells>, tenant: u64, k: &str, cmd: Cmd) -> Executed<Cells> {
    let idem = key(k, &cmd);
    tokio::time::timeout(T, engine.execute(actor(tenant), cmd, idem))
        .await
        .expect("in time")
}

fn stat(engine: &PgEngine<Cells>) -> [u64; 5] {
    let s = engine.stats();
    let l = |a: &AtomicU64| a.load(Ordering::Relaxed);
    [
        l(&s.attempts),
        l(&s.retries),
        l(&s.commits),
        l(&s.replays),
        l(&s.reads),
    ]
}

fn loads(engine: &PgEngine<Cells>) -> u64 {
    engine.stats().loads.load(Ordering::Relaxed)
}

/// An outside transaction that changes cell 0 of `tenant` after the attempt's snapshot, and
/// advances the tenant's version as an engine's commit does.
async fn conflict(admin: &tokio_postgres::Client, tenant: u64) {
    admin
        .execute(
            "WITH u AS (UPDATE cells SET v = v + 100 WHERE tenant_id = $1 AND id = 0 RETURNING 1) \
             INSERT INTO leanharbor_version (tenant_id, version) SELECT $1, 1 FROM u \
             ON CONFLICT (tenant_id) DO UPDATE SET version = leanharbor_version.version + 1",
            &[&(tenant as i64)],
        )
        .await
        .unwrap();
}

// Items 1 and 2: one attempt is one SERIALIZABLE read-write transaction; a retry is a new
// transaction that reads the rows again and calls `transition` again.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn serialization_failures_retry_in_a_new_transaction() {
    let db = setup("contract_ssi").await;
    let admin = db.admin.clone();
    let (hook, seen) = hook_at(Point::Loaded, 2, move |a| {
        let admin = admin.clone();
        async move { conflict(&admin, a.tenant).await }
    });
    let plain = db.engine(1, Config::default()).await;
    run(&plain, 1, add(0, 5)).await.unwrap().unwrap();
    let pg = db.engine(2, config(20, true, Some(hook))).await;
    let r = run(&pg, 1, add(0, 1)).await.unwrap().unwrap();
    assert_eq!(stat(&pg)[0], 3, "attempts");
    assert_eq!(stat(&pg)[1], 2, "retries");
    // Each retry read the outside commits made after the snapshot of the attempt before it.
    assert_eq!(r, 5 + 100 + 100 + 1);
    assert_eq!(db.cell(1, 0).await, Some(206));
    let txs: Vec<_> = seen
        .at(Point::Loaded)
        .into_iter()
        .map(|a| a.tx.unwrap())
        .collect();
    assert_eq!(txs.len(), 3);
    for tx in &txs {
        assert_eq!(tx.isolation, "serializable");
        assert!(!tx.read_only);
    }
    assert!(txs[0].vxid != txs[1].vxid && txs[1].vxid != txs[2].vxid);
}

// Item 2: retries stop after `max_attempts` with `RetriesExhausted`, and no attempt left a write
// or a stored reply.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn serialization_failures_exhaust_after_max_attempts() {
    let db = setup("contract_exhaust").await;
    let admin = db.admin.clone();
    let (hook, _) = hook_at(Point::Loaded, u64::MAX, move |a| {
        let admin = admin.clone();
        async move { conflict(&admin, a.tenant).await }
    });
    let plain = db.engine(1, Config::default()).await;
    run(&plain, 1, add(0, 5)).await.unwrap().unwrap();
    let pg = db.engine(2, config(3, true, Some(hook))).await;
    let r = run_keyed(&pg, 1, "k", add(0, 1)).await;
    assert_eq!(r, Err(EngineError::RetriesExhausted));
    assert_eq!(stat(&pg)[0], 3, "attempts");
    assert_eq!(db.cell(1, 0).await, Some(305), "only the outside writes");
    assert_eq!(db.replies(1).await, 0);
}

// Item 2 (deadlock): the attempt holds the tenant's advisory lock and waits for a row an outside
// transaction holds, which then waits for the advisory lock. PostgreSQL aborts the attempt with
// 40P01 (the outside session waits 30 s before it checks), and the retry succeeds.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn deadlocks_are_retried() {
    let db = setup("contract_deadlock").await;
    let other = Arc::new(connect(&db.admin_url()).await);
    let outside: Arc<Mutex<Option<Outside>>> = Arc::default();
    let o = outside.clone();
    let (hook, _) = hook_at(Point::Loaded, 1, move |a| {
        let (other, o) = (other.clone(), o.clone());
        async move {
            other
                .batch_execute(&format!(
                    "BEGIN; SET LOCAL deadlock_timeout = '30s'; \
                     UPDATE cells SET v = v WHERE tenant_id = {} AND id = 0",
                    a.tenant
                ))
                .await
                .unwrap();
            let (pid, tenant) = (a.pid, a.tenant as i64);
            let task = tokio::spawn(async move {
                loop {
                    let n: i64 = other
                        .query_one(
                            "SELECT count(*) FROM pg_locks WHERE pid = $1 AND NOT granted",
                            &[&pid],
                        )
                        .await?
                        .get(0);
                    if n > 0 {
                        break;
                    }
                    tokio::time::sleep(Duration::from_millis(5)).await;
                }
                other
                    .execute("SELECT pg_advisory_xact_lock($1)", &[&tenant])
                    .await?;
                other.batch_execute("ROLLBACK").await
            });
            *o.lock().unwrap() = Some(task);
        }
    });
    let pg = db.engine(2, config(20, true, Some(hook))).await;
    let plain = db.engine(1, Config::default()).await;
    run(&plain, 1, add(0, 5)).await.unwrap().unwrap();
    let r = run(&pg, 1, add(0, 1)).await.unwrap().unwrap();
    let task = outside.lock().unwrap().take().unwrap();
    task.await.unwrap().unwrap();
    assert_eq!(stat(&pg)[1], 1, "one retry, after the deadlock");
    assert_eq!(r, 6);
    assert_eq!(db.cell(1, 0).await, Some(6));
    assert_eq!(db.no_advisory_locks(Duration::from_secs(2)).await, 0);
}

// Item 2 (lost connection): a backend terminated before COMMIT (at each point of an attempt)
// retries from BEGIN on a new connection, and the command takes effect once, with or without a
// key. Without a key, a connection lost right before COMMIT and noticed only by COMMIT is
// `CommitUnknown` (it did not commit; the engine cannot know that).
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn killed_before_commit_retries_once() {
    let db = setup("contract_kill").await;
    let mut tenant = 0;
    for point in [Point::Locked, Point::Loaded, Point::Written] {
        for keyed in [false, true] {
            tenant += 1;
            let admin = db.admin.clone();
            let (hook, seen) = hook_at(point, 1, move |a| {
                let admin = admin.clone();
                async move { kill(&admin, a.pid).await }
            });
            let pg = db.engine(2, config(20, true, Some(hook))).await;
            let cmd = add(0, 7);
            let r = if keyed {
                run_keyed(&pg, tenant, "k", cmd).await
            } else {
                run(&pg, tenant, cmd).await
            };
            let case = format!("{point:?}, keyed {keyed}");
            if point == Point::Written && !keyed {
                assert_eq!(r, Err(EngineError::CommitUnknown), "{case}");
                assert_eq!(db.cell(tenant, 0).await, None, "{case}: not committed");
            } else {
                assert_eq!(r, Ok(Ok(7)), "{case}");
                assert_eq!(db.cell(tenant, 0).await, Some(7), "{case}: once");
                assert_eq!(stat(&pg)[1], 1, "{case}: one retry");
                let pids: Vec<i32> = seen.at(point).iter().map(|a| a.pid).collect();
                assert_eq!(pids.len(), 2, "{case}");
                assert_ne!(pids[0], pids[1], "{case}: a new connection");
            }
            assert_eq!(
                db.replies(tenant).await,
                i64::from(keyed && r.is_ok()),
                "{case}"
            );
        }
    }
    assert_eq!(db.no_advisory_locks(Duration::from_secs(2)).await, 0);
}

// Item 3: a refused command rolls back and stores no row and no reply, with or without a key.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn refusals_write_nothing() {
    let db = setup("contract_refusal").await;
    let pg = db.engine(2, Config::default()).await;
    run(&pg, 1, add(0, 5)).await.unwrap().unwrap();
    let before = stat(&pg);
    assert_eq!(run(&pg, 1, add(0, -10)).await, Ok(Err(Refused::Negative)));
    assert_eq!(
        run_keyed(&pg, 1, "k", add(0, -10)).await,
        Ok(Err(Refused::Negative))
    );
    let move_ = Cmd::Move {
        from: 0,
        to: 1,
        amount: 50,
    };
    assert_eq!(run(&pg, 1, move_).await, Ok(Err(Refused::Negative)));
    assert_eq!(stat(&pg)[2], before[2], "no commit");
    assert_eq!(db.cells(1).await, BTreeMap::from([(0, 5)]));
    assert_eq!(db.replies(1).await, 0);
    // The refusal stored no reply under its key: the same command runs again once it is
    // accepted.
    run(&pg, 1, add(0, 20)).await.unwrap().unwrap();
    assert_eq!(run_keyed(&pg, 1, "k", add(0, -10)).await, Ok(Ok(15)));
    assert_eq!(db.replies(1).await, 1);
}

// Item 4: the app's writes and the stored reply commit together. A COMMIT lost before the
// server ran it leaves neither; one lost after the server committed leaves both.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn replies_commit_with_the_writes() {
    let db = setup("contract_atomic").await;
    let proxy = Proxy::start(cluster()).await;
    let pg = db
        .engine_at(&proxy.url(&db.name), 1, config(1, true, None))
        .await;
    proxy.arm(Fault::DropBefore);
    let r = run_keyed(&pg, 1, "a", add(0, 3)).await;
    assert_eq!(
        r,
        Err(EngineError::RetriesExhausted),
        "one attempt, COMMIT lost"
    );
    assert_eq!(db.cell(1, 0).await, None);
    assert_eq!(db.replies(1).await, 0);
    proxy.arm(Fault::DropAfter);
    let r = run_keyed(&pg, 2, "a", add(0, 3)).await;
    assert_eq!(
        r,
        Err(EngineError::RetriesExhausted),
        "one attempt, COMMIT lost"
    );
    assert_eq!(db.cell(2, 0).await, Some(3));
    assert_eq!(db.replies(2).await, 1);
    assert_eq!(proxy.outcomes(), vec![Outcome::NotSent, Outcome::Committed]);
}

// Item 4: a reply is stored per tenant, scope and key; the same key with the same command
// replays it without running the command, and with another command is refused.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn idempotency_keys_replay_and_conflict() {
    let db = setup("contract_keys").await;
    let pg = db.engine(2, Config::default()).await;
    assert_eq!(run_keyed(&pg, 1, "k", add(0, 2)).await, Ok(Ok(2)));
    assert_eq!(run_keyed(&pg, 1, "k", add(0, 2)).await, Ok(Ok(2)));
    assert_eq!(stat(&pg)[3], 1, "one replay");
    assert_eq!(db.cell(1, 0).await, Some(2), "ran once");
    assert_eq!(
        run_keyed(&pg, 1, "k", add(0, 3)).await,
        Err(EngineError::IdempotencyConflict)
    );
    let other_scope = Some(Idempotency {
        scope: "u2".to_owned(),
        key: "k".to_owned(),
        fingerprint: format!("{:?}", add(0, 2)).into_bytes(),
    });
    let r = pg.execute(actor(1), add(0, 2), other_scope).await;
    assert_eq!(r, Ok(Ok(4)), "another scope runs the command");
    assert_eq!(
        run_keyed(&pg, 2, "k", add(0, 3)).await,
        Ok(Ok(3)),
        "another tenant"
    );
    assert_eq!(db.cell(1, 0).await, Some(4));
    assert_eq!(db.replies(1).await, 2);
}

// Item 4: concurrent requests with one key run the command once; the others replay its reply
// (a loser of the race for the key's row gets 23505 and retries).
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn concurrent_requests_with_one_key_run_once() {
    let db = setup("contract_one_key").await;
    for (tenant, lock) in [(1, true), (2, false)] {
        let pg = Arc::new(db.engine(8, config(20, lock, None)).await);
        let mut tasks = Vec::new();
        for _ in 0..32 {
            let pg = pg.clone();
            tasks.push(tokio::spawn(async move {
                run_keyed(&pg, tenant, "once", add(0, 1)).await
            }));
        }
        for task in tasks {
            assert_eq!(task.await.unwrap(), Ok(Ok(1)), "lock {lock}");
        }
        assert_eq!(db.cell(tenant, 0).await, Some(1), "lock {lock}");
        assert_eq!(db.replies(tenant).await, 1);
        assert_eq!(stat(&pg)[2], 1, "one commit");
        assert_eq!(stat(&pg)[3], 31, "31 replays");
    }
}

// Item 5: the tenant's advisory lock is held from before BEGIN to before the connection returns
// to the pool. A request queued behind it waits in `pg_advisory_lock` before its transaction, so
// it reads the first request's commit and commits without a retry.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn advisory_lock_is_held_around_the_transaction() {
    let db = setup("contract_lock").await;
    let release = Arc::new(Notify::new());
    let admin = db.admin.clone();
    let held = Arc::new(Mutex::new(Vec::new()));
    let (h, r) = (held.clone(), release.clone());
    let (hook, _) = hook_at(Point::Written, 1, move |a| {
        let (admin, h, r) = (admin.clone(), h.clone(), r.clone());
        async move {
            let n: i64 = admin
                .query_one(
                    "SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND granted \
                     AND pid = $1 AND objid = $2",
                    &[&a.pid, &(a.tenant as u32)],
                )
                .await
                .unwrap()
                .get(0);
            h.lock().unwrap().push(n);
            r.notified().await;
        }
    });
    let pg = Arc::new(db.engine(2, config(20, true, Some(hook))).await);
    let first = {
        let pg = pg.clone();
        tokio::spawn(async move { run(&pg, 1, add(0, 1)).await })
    };
    while held.lock().unwrap().is_empty() {
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    assert_eq!(held.lock().unwrap()[0], 1, "the lock is held before COMMIT");
    let second = {
        let pg = pg.clone();
        tokio::spawn(async move { run(&pg, 1, add(0, 10)).await })
    };
    let waiting = loop {
        let row = db
            .admin
            .query_opt(
                "SELECT l.pid FROM pg_locks l JOIN pg_stat_activity a ON a.pid = l.pid \
                 WHERE l.locktype = 'advisory' AND NOT l.granted AND a.query = $1 \
                 AND a.datname = current_database()",
                &[&"SELECT pg_advisory_lock($1)"],
            )
            .await
            .unwrap();
        if let Some(row) = row {
            break row.get::<_, i32>(0);
        }
        tokio::time::sleep(Duration::from_millis(5)).await;
    };
    // The waiting request has not read the table: it holds no lock on it, not even the
    // predicate lock of a SERIALIZABLE read.
    let read: i64 = db
        .admin
        .query_one(
            "SELECT count(*) FROM pg_locks WHERE pid = $1 AND relation = 'cells'::regclass",
            &[&waiting],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(read, 0);
    release.notify_one();
    assert_eq!(first.await.unwrap(), Ok(Ok(1)));
    assert_eq!(
        second.await.unwrap(),
        Ok(Ok(11)),
        "it read the first commit"
    );
    assert_eq!(stat(&pg)[1], 0, "no retry");
    assert_eq!(db.no_advisory_locks(Duration::from_secs(2)).await, 0);
}

// Item 5: no advisory lock is left after a commit, a refusal, an attempt whose backend was
// terminated, a failed request, or a caller that stopped waiting; the pool keeps its
// connections and another engine gets the tenant at once.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn advisory_locks_are_released() {
    let db = setup("contract_release").await;
    let admin = db.admin.clone();
    let (hook, _) = hook_at(Point::Loaded, 1, move |a| {
        let admin = admin.clone();
        async move { kill(&admin, a.pid).await }
    });
    let pg = db.engine(2, config(20, true, Some(hook))).await;
    run(&pg, 1, add(0, 5)).await.unwrap().unwrap();
    assert_eq!(
        db.no_advisory_locks(Duration::from_secs(2)).await,
        0,
        "killed"
    );
    run(&pg, 1, add(0, 1)).await.unwrap().unwrap();
    assert_eq!(db.advisory_locks().await, 0, "commit");
    assert_eq!(run(&pg, 1, add(0, -100)).await, Ok(Err(Refused::Negative)));
    assert_eq!(db.advisory_locks().await, 0, "refusal");
    run_keyed(&pg, 1, "k", add(0, 1)).await.unwrap().unwrap();
    let conflict = run_keyed(&pg, 1, "k", add(0, 2)).await;
    assert_eq!(conflict, Err(EngineError::IdempotencyConflict));
    assert_eq!(db.advisory_locks().await, 0, "failed request");

    let release = Arc::new(Notify::new());
    let r = release.clone();
    let (hook, seen) = hook_at(Point::Written, 1, move |_| {
        let r = r.clone();
        async move { r.notified().await }
    });
    let blocked = Arc::new(db.engine(2, config(20, true, Some(hook))).await);
    let caller = {
        let blocked = blocked.clone();
        tokio::spawn(async move { blocked.execute(actor(1), add(0, 100), None).await })
    };
    while seen.at(Point::Written).is_empty() {
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    caller.abort();
    assert!(
        caller.await.unwrap_err().is_cancelled(),
        "the caller stopped waiting"
    );
    release.notify_one();
    assert_eq!(
        db.no_advisory_locks(Duration::from_secs(5)).await,
        0,
        "dropped"
    );
    // The request ran to its end in its own task: its command committed once.
    assert_eq!(db.cell(1, 0).await, Some(107));
    let other = db.engine(1, config(1, true, None)).await;
    let r = tokio::time::timeout(
        Duration::from_secs(2),
        other.execute(actor(1), add(0, 1), None),
    )
    .await
    .expect("the tenant is free");
    assert_eq!(r, Ok(Ok(108)));
    assert_eq!(blocked.idle(), 1, "the connection is back in the pool");
}

// Item 6: a read-only command runs in one SERIALIZABLE READ ONLY DEFERRABLE transaction without
// the advisory lock, is retried after a lost connection, and fails if it writes; with a key it
// takes the write path.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn read_only_path() {
    let db = setup("contract_read").await;
    let admin = db.admin.clone();
    let locks = Arc::new(Mutex::new(Vec::new()));
    let l = locks.clone();
    let (hook, seen) = hook_at(Point::Loaded, u64::MAX, move |a| {
        let (admin, l) = (admin.clone(), l.clone());
        async move {
            let n: i64 = admin
                .query_one(
                    "SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND pid = $1",
                    &[&a.pid],
                )
                .await
                .unwrap()
                .get(0);
            l.lock().unwrap().push(n);
        }
    });
    let pg = db.engine(2, config(20, true, Some(hook))).await;
    run(&pg, 1, add(0, 5)).await.unwrap().unwrap();
    let before = stat(&pg);
    assert_eq!(run(&pg, 1, Cmd::Get { cell: 0 }).await, Ok(Ok(5)));
    assert_eq!(stat(&pg)[4] - before[4], 1, "one read");
    let read = seen.at(Point::Loaded).pop().unwrap();
    let tx = read.tx.unwrap();
    assert_eq!(tx.isolation, "serializable");
    assert!(tx.read_only && tx.deferrable);
    assert_eq!(locks.lock().unwrap().last(), Some(&0), "no advisory lock");
    assert!(
        seen.at(Point::Locked).len() == 1,
        "only the write took the lock"
    );

    // A command that claims to read only and writes fails, and nothing is stored.
    let r = run(&pg, 1, Cmd::Poke { cell: 0 }).await;
    assert!(matches!(r, Err(EngineError::Broken(_))), "{r:?}");
    assert_eq!(db.cell(1, 0).await, Some(5));

    // With a key, a read takes the write path and stores its reply.
    let before = stat(&pg);
    assert_eq!(
        run_keyed(&pg, 1, "r", Cmd::Get { cell: 0 }).await,
        Ok(Ok(5))
    );
    assert_eq!(stat(&pg)[4], before[4], "not a read");
    let keyed = seen.at(Point::Loaded).pop().unwrap().tx.unwrap();
    assert!(!keyed.read_only);
    assert_eq!(db.replies(1).await, 1);

    // A lost connection is retried.
    let admin = db.admin.clone();
    let (hook, seen) = hook_at(Point::Loaded, 1, move |a| {
        let admin = admin.clone();
        async move { kill(&admin, a.pid).await }
    });
    let killed = db.engine(2, config(20, true, Some(hook))).await;
    assert_eq!(run(&killed, 1, Cmd::Get { cell: 0 }).await, Ok(Ok(5)));
    assert_eq!(stat(&killed)[4], 2, "two reads");
    assert_eq!(seen.at(Point::Loaded).len(), 2);
}

// Item 7: without a key, a COMMIT lost before or after the server ran it is `CommitUnknown`,
// not retried; the first did not commit and the second did.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn lost_commit_without_key_is_unknown() {
    let db = setup("contract_unknown").await;
    let proxy = Proxy::start(cluster()).await;
    let pg = db
        .engine_at(&proxy.url(&db.name), 1, config(20, true, None))
        .await;
    proxy.arm(Fault::DropBefore);
    assert_eq!(
        run(&pg, 1, add(0, 3)).await,
        Err(EngineError::CommitUnknown)
    );
    proxy.arm(Fault::DropAfter);
    assert_eq!(
        run(&pg, 2, add(0, 3)).await,
        Err(EngineError::CommitUnknown)
    );
    assert_eq!(stat(&pg)[1], 0, "not retried");
    assert_eq!(db.cell(1, 0).await, None);
    assert_eq!(db.cell(2, 0).await, Some(3));
    assert_eq!(proxy.outcomes(), vec![Outcome::NotSent, Outcome::Committed]);
}

// Item 7, with a key: a lost COMMIT is retried, and the command takes effect once; after a
// COMMIT the server ran, the retry replays the stored reply.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn lost_commit_with_key_runs_once() {
    let db = setup("contract_lost_keyed").await;
    let proxy = Proxy::start(cluster()).await;
    let pg = db
        .engine_at(&proxy.url(&db.name), 1, config(20, true, None))
        .await;
    proxy.arm(Fault::DropBefore);
    assert_eq!(run_keyed(&pg, 1, "k", add(0, 3)).await, Ok(Ok(3)));
    proxy.arm(Fault::DropAfter);
    assert_eq!(run_keyed(&pg, 2, "k", add(0, 3)).await, Ok(Ok(3)));
    assert_eq!(db.cell(1, 0).await, Some(3));
    assert_eq!(db.cell(2, 0).await, Some(3));
    assert_eq!(stat(&pg)[3], 1, "the second replayed");
    assert_eq!(proxy.outcomes(), vec![Outcome::NotSent, Outcome::Committed]);
}

// With PostgreSQL's SERIALIZABLE, whose commits equal a serial order: 64 clients move units
// between four cells of one tenant, with and without the advisory lock. The total is kept, and
// each cell holds what the accepted moves left there.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn concurrent_moves_are_serial() {
    let db = setup("contract_serial").await;
    for (tenant, lock) in [(1, true), (2, false)] {
        let pg = Arc::new(db.engine(8, config(1000, lock, None)).await);
        for cell in 0..4 {
            run(&pg, tenant, add(cell, 100)).await.unwrap().unwrap();
        }
        let mut tasks = Vec::new();
        for client in 0..64_i64 {
            let pg = pg.clone();
            tasks.push(tokio::spawn(async move {
                let mut moved = Vec::new();
                for i in 0..8 {
                    let (from, to) = ((client + i) % 4, (client + i + 1) % 4);
                    let cmd = Cmd::Move {
                        from,
                        to,
                        amount: 1,
                    };
                    if let Ok(Ok(_)) = pg.execute(actor(tenant), cmd, None).await {
                        moved.push((from, to));
                    }
                }
                moved
            }));
        }
        let mut expected = BTreeMap::from([(0, 100), (1, 100), (2, 100), (3, 100)]);
        let mut accepted = 0;
        for task in tasks {
            for (from, to) in task.await.unwrap() {
                *expected.get_mut(&from).unwrap() -= 1;
                *expected.get_mut(&to).unwrap() += 1;
                accepted += 1;
            }
        }
        assert_eq!(accepted, 512, "lock {lock}");
        assert_eq!(db.cells(tenant).await, expected, "lock {lock}");
        if lock {
            assert_eq!(stat(&pg)[1], 0, "the lock spares every retry");
        }
    }
}

fn get(cell: i64) -> Cmd {
    Cmd::Get { cell }
}

// Item 8: an engine reads the rows another engine wrote, whichever path it takes, and reads no
// row while the version is the one it remembers.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn other_engines_writes_are_read() {
    let db = setup("contract_other").await;
    let a = db.engine(2, Config::default()).await;
    let b = db.engine(2, Config::default()).await;
    assert_eq!(run(&a, 1, add(0, 5)).await, Ok(Ok(5)));
    assert_eq!(loads(&a), 1);
    assert_eq!(run(&a, 1, get(0)).await, Ok(Ok(5)));
    assert_eq!(run(&a, 1, add(0, 1)).await, Ok(Ok(6)));
    assert_eq!(loads(&a), 1, "the remembered snapshot, on both paths");
    assert_eq!(run(&b, 1, add(0, 10)).await, Ok(Ok(16)));
    assert_eq!(run(&a, 1, get(0)).await, Ok(Ok(16)), "the read-only path");
    assert_eq!(loads(&a), 2);
    let cmd = Cmd::Move {
        from: 0,
        to: 1,
        amount: 6,
    };
    assert_eq!(run(&b, 1, cmd).await, Ok(Ok(10)));
    assert_eq!(run(&a, 1, add(1, 1)).await, Ok(Ok(7)), "the write path");
    assert_eq!(run_keyed(&b, 1, "k", get(0)).await, Ok(Ok(10)), "keyed");
    assert_eq!(run(&b, 1, get(1)).await, Ok(Ok(7)));
    assert_eq!(loads(&a), 3);
    assert_eq!(loads(&b), 2, "its own commit remembered");
    assert_eq!(db.cells(1).await, BTreeMap::from([(0, 10), (1, 7)]));
}

// Item 8, on PostgreSQL's side: two transactions that read a tenant's version and advance it
// cannot both commit, whether the row exists or not. The second fails with 40001, which the
// engines retry, and not with 23505.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn version_rows_conflict() {
    const ADVANCE: &str = "INSERT INTO leanharbor_version (tenant_id, version) VALUES ($1, 1) \
        ON CONFLICT (tenant_id) DO UPDATE SET version = leanharbor_version.version + 1 \
        RETURNING version";
    let db = setup("contract_version").await;
    let pg = db.engine(1, Config::default()).await;
    run(&pg, 2, add(0, 1)).await.unwrap().unwrap();
    for (tenant, before) in [(1_i64, 0_i64), (2, 1)] {
        let first = connect(&db.url).await;
        let second = Arc::new(connect(&db.url).await);
        for c in [&first, &*second] {
            c.batch_execute("BEGIN ISOLATION LEVEL SERIALIZABLE")
                .await
                .unwrap();
            let read: Option<i64> = c
                .query_opt(
                    "SELECT version FROM leanharbor_version WHERE tenant_id = $1",
                    &[&tenant],
                )
                .await
                .unwrap()
                .map(|r| r.get(0));
            assert_eq!(read.unwrap_or(0), before);
        }
        let advanced: i64 = first.query_one(ADVANCE, &[&tenant]).await.unwrap().get(0);
        assert_eq!(advanced, before + 1);
        let s = second.clone();
        let waiting = tokio::spawn(async move { s.query_one(ADVANCE, &[&tenant]).await });
        tokio::time::sleep(Duration::from_millis(200)).await;
        assert!(!waiting.is_finished(), "tenant {tenant}: waits for the first");
        first.batch_execute("COMMIT").await.unwrap();
        let e = waiting.await.unwrap().unwrap_err();
        assert_eq!(
            e.code(),
            Some(&tokio_postgres::error::SqlState::T_R_SERIALIZATION_FAILURE),
            "tenant {tenant}: {e}"
        );
        second.batch_execute("ROLLBACK").await.unwrap();
    }
}

// Item 8: a COMMIT of unknown outcome forgets the tenant's snapshot. The engine reads the rows
// again, whether the COMMIT ran or not, and after another engine's commit.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn lost_commit_forgets_the_snapshot() {
    let db = setup("contract_forget").await;
    let proxy = Proxy::start(cluster()).await;
    let pg = db
        .engine_at(&proxy.url(&db.name), 1, config(20, true, None))
        .await;
    let other = db.engine(1, Config::default()).await;
    assert_eq!(run(&pg, 1, add(0, 5)).await, Ok(Ok(5)));
    proxy.arm(Fault::DropBefore);
    assert_eq!(run(&pg, 1, add(0, 1)).await, Err(EngineError::CommitUnknown));
    assert_eq!(run(&pg, 1, get(0)).await, Ok(Ok(5)), "not committed");
    assert_eq!(run(&other, 1, add(0, 10)).await, Ok(Ok(15)));
    assert_eq!(run(&pg, 1, get(0)).await, Ok(Ok(15)), "the other engine's commit");
    proxy.arm(Fault::DropAfter);
    assert_eq!(run(&pg, 1, add(0, 1)).await, Err(EngineError::CommitUnknown));
    assert_eq!(run(&pg, 1, add(0, 1)).await, Ok(Ok(17)), "committed");
    assert_eq!(run(&other, 1, get(0)).await, Ok(Ok(17)));
    assert_eq!(loads(&pg), 4, "every attempt after a lost COMMIT reads the rows");
    assert_eq!(proxy.outcomes(), vec![Outcome::NotSent, Outcome::Committed]);
}

// Item 8: a refusal, and an attempt rolled back by a terminated backend, leave the remembered
// snapshot as the last commit left it: the refusal reads no row, and the retry runs the command
// on what was committed.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn refusals_and_rollbacks_keep_the_snapshot() {
    let db = setup("contract_keep").await;
    let admin = db.admin.clone();
    let armed = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let arm = armed.clone();
    let (hook, _) = hook_at(Point::Written, u64::MAX, move |a| {
        let (admin, armed) = (admin.clone(), armed.clone());
        async move {
            if armed.swap(false, Ordering::SeqCst) {
                kill(&admin, a.pid).await;
            }
        }
    });
    let pg = db.engine(2, config(20, true, Some(hook))).await;
    assert_eq!(run(&pg, 1, add(0, 5)).await, Ok(Ok(5)));
    assert_eq!(run(&pg, 1, add(0, -6)).await, Ok(Err(Refused::Negative)));
    assert_eq!(run_keyed(&pg, 1, "k", add(0, -6)).await, Ok(Err(Refused::Negative)));
    assert_eq!(run(&pg, 1, get(0)).await, Ok(Ok(5)));
    assert_eq!(run(&pg, 1, add(0, 1)).await, Ok(Ok(6)));
    assert_eq!(loads(&pg), 1, "one read of the rows");
    let fresh = db.engine(2, Config::default()).await;
    assert_eq!(run(&fresh, 1, add(0, -7)).await, Ok(Err(Refused::Negative)));
    assert_eq!(run(&fresh, 1, get(0)).await, Ok(Ok(6)));
    assert_eq!(loads(&fresh), 1, "the snapshot loaded for a refusal");
    let before = loads(&pg);
    assert_eq!(run(&pg, 2, add(0, 3)).await, Ok(Ok(3)));
    arm.store(true, Ordering::SeqCst);
    assert_eq!(run(&pg, 2, add(0, 4)).await, Err(EngineError::CommitUnknown));
    assert_eq!(run(&pg, 2, add(0, 4)).await, Ok(Ok(7)), "on the committed rows");
    assert_eq!(db.cell(2, 0).await, Some(7));
    assert_eq!(run(&pg, 3, add(0, 3)).await, Ok(Ok(3)));
    arm.store(true, Ordering::SeqCst);
    assert_eq!(run_keyed(&pg, 3, "k", add(0, 4)).await, Ok(Ok(7)), "retried");
    assert_eq!(db.cell(3, 0).await, Some(7));
    assert_eq!(loads(&pg) - before, 4);
}

// Item 8: the engine remembers at most `cache_tenants` tenants and forgets the one it used
// least recently; with 0 it remembers none.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn remembers_at_most_cache_tenants() {
    let db = setup("contract_capacity").await;
    let two = Config {
        cache_tenants: 2,
        ..Config::default()
    };
    let pg = db.engine(1, two).await;
    for tenant in 1..=3 {
        run(&pg, tenant, add(0, 1)).await.unwrap().unwrap();
    }
    assert_eq!(pg.cached(), 2);
    assert_eq!(loads(&pg), 3);
    assert_eq!(run(&pg, 2, get(0)).await, Ok(Ok(1)));
    assert_eq!(loads(&pg), 3, "tenant 2 remembered");
    assert_eq!(run(&pg, 1, get(0)).await, Ok(Ok(1)));
    assert_eq!(loads(&pg), 4, "tenant 1 forgotten");
    assert_eq!(run(&pg, 2, get(0)).await, Ok(Ok(1)));
    assert_eq!(run(&pg, 1, get(0)).await, Ok(Ok(1)));
    assert_eq!(loads(&pg), 4, "tenants 1 and 2 remembered");
    assert_eq!(run(&pg, 3, get(0)).await, Ok(Ok(1)));
    assert_eq!(loads(&pg), 5, "tenant 3 forgotten");
    assert_eq!(pg.cached(), 2);
    let none = Config {
        cache_tenants: 0,
        ..Config::default()
    };
    let pg = db.engine(1, none).await;
    for _ in 0..3 {
        run(&pg, 1, add(0, 1)).await.unwrap().unwrap();
        run(&pg, 1, get(0)).await.unwrap().unwrap();
    }
    assert_eq!(pg.cached(), 0);
    assert_eq!(loads(&pg), 6);
}

// Item 8 with SERIALIZABLE: two engines, each with 32 clients, move units between four cells of
// one tenant, with and without the advisory lock. Every cell holds what the accepted moves left,
// and both engines then read it.
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn concurrent_engines_are_serial() {
    let db = setup("contract_engines").await;
    for (tenant, lock) in [(1, true), (2, false)] {
        let engines = [
            Arc::new(db.engine(4, config(1000, lock, None)).await),
            Arc::new(db.engine(4, config(1000, lock, None)).await),
        ];
        for cell in 0..4 {
            run(&engines[0], tenant, add(cell, 100)).await.unwrap().unwrap();
        }
        let mut tasks = Vec::new();
        for client in 0..64_i64 {
            let pg = engines[(client % 2) as usize].clone();
            tasks.push(tokio::spawn(async move {
                let mut moved = Vec::new();
                for i in 0..8 {
                    let (from, to) = ((client + i) % 4, (client + i + 1) % 4);
                    let cmd = Cmd::Move {
                        from,
                        to,
                        amount: 1,
                    };
                    if let Ok(Ok(_)) = pg.execute(actor(tenant), cmd, None).await {
                        moved.push((from, to));
                    }
                    let _ = pg.execute(actor(tenant), get(from), None).await;
                }
                moved
            }));
        }
        let mut expected = BTreeMap::from([(0, 100), (1, 100), (2, 100), (3, 100)]);
        let mut accepted = 0;
        for task in tasks {
            for (from, to) in task.await.unwrap() {
                *expected.get_mut(&from).unwrap() -= 1;
                *expected.get_mut(&to).unwrap() += 1;
                accepted += 1;
            }
        }
        assert_eq!(accepted, 512, "lock {lock}");
        assert_eq!(db.cells(tenant).await, expected, "lock {lock}");
        for pg in &engines {
            for (cell, v) in &expected {
                assert_eq!(run(pg, tenant, get(*cell)).await, Ok(Ok(*v)), "lock {lock}");
            }
        }
    }
}

// The role split: the tables belong to a role that cannot log in, and the engine's role reads
// and writes their rows but cannot alter, drop or truncate them. `lockdown` refuses a
// superuser and can run again; the engine starts on the tables it made.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn roles_keep_the_engine_to_rows() {
    let db = setup("contract_roles").await;
    let owner: String = db
        .admin
        .query_one(
            "SELECT tableowner FROM pg_tables WHERE tablename = 'cells'",
            &[],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(owner, OWNER);
    let engine = connect(&db.url).await;
    for statement in [
        "DROP TABLE cells",
        "TRUNCATE cells",
        "ALTER TABLE cells ADD COLUMN x BIGINT",
        "DROP TABLE leanharbor_idempotency",
        "DROP TABLE leanharbor_version",
        "TRUNCATE leanharbor_version",
    ] {
        let e = engine.batch_execute(statement).await.unwrap_err();
        assert_eq!(
            e.code(),
            Some(&tokio_postgres::error::SqlState::INSUFFICIENT_PRIVILEGE),
            "{statement}"
        );
    }
    let pg = db.engine(1, Config::default()).await;
    assert_eq!(run(&pg, 1, add(0, 1)).await, Ok(Ok(1)));
    lockdown::<Cells>(&db.admin_url(), OWNER, ENGINE_ROLE)
        .await
        .expect("lockdown runs again");
    let refused = lockdown::<Cells>(&db.admin_url(), OWNER, "postgres").await;
    assert!(
        matches!(refused, Err(EngineError::Broken(_))),
        "{refused:?}"
    );
    let login = lockdown::<Cells>(&db.admin_url(), ENGINE_ROLE, OWNER).await;
    assert!(matches!(login, Err(EngineError::Broken(_))), "{login:?}");
    assert_eq!(db.cell(1, 0).await, Some(1));
}
