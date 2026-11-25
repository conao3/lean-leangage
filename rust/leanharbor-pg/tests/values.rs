//! Every kind of `Val`, `NULL` included, written by the engine and read back unchanged, in a
//! table whose name holds `"`, a space and a letter outside ASCII. The engine remembers no
//! snapshot, so every command reads the rows back. A text holding NUL, which
//! PostgreSQL cannot store, fails the command instead of storing something else.

use leanfran::runtime::Nat;
use leanharbor::sql::{Col, Kind, Tab, Val, Write};
use leanharbor::{Engine, EngineError, Kernel, Storage};
use leanharbor_pg::testing::cluster;
use leanharbor_pg::{Config, PgEngine};

/// Rows of one table, stored as the commands give them.
struct Rows;

#[derive(Clone, Debug)]
enum Cmd {
    Put(Vec<Val>),
    Read,
}

type Table = Vec<Vec<Val>>;

impl Kernel for Rows {
    type Principal = u64;
    type Snapshot = Table;
    type View = Table;
    type Command = Cmd;
    type WriteSet = Table;
    type Reply = Table;
    type Error = ();

    fn init() -> Table {
        Vec::new()
    }

    fn tenant(actor: &u64) -> u64 {
        *actor
    }

    fn lend<R>(snap: &mut Table, f: impl FnOnce(Table) -> (Table, R)) -> R {
        let (view, r) = f(std::mem::take(snap));
        *snap = view;
        r
    }

    fn transition(_: &u64, snap: &Table, cmd: &Cmd) -> Result<(Table, Table), ()> {
        match cmd {
            Cmd::Put(row) => Ok((vec![row.clone()], Vec::new())),
            Cmd::Read => Ok((Vec::new(), snap.clone())),
        }
    }

    fn apply(mut snap: Table, ws: Table) -> Table {
        for row in ws {
            snap.retain(|r| r[0] != row[0]);
            snap.push(row);
        }
        snap
    }

    fn read_only(cmd: &Cmd) -> bool {
        matches!(cmd, Cmd::Read)
    }
}

fn col(name: &str, kind: Kind, nullable: bool) -> Col {
    Col {
        name: name.to_owned(),
        kind,
        nullable,
    }
}

impl Storage for Rows {
    fn tables() -> Vec<Tab> {
        vec![Tab {
            name: "odd \"näme\"".to_owned(),
            cols: vec![
                col("k", Kind::Int, false),
                col("b", Kind::Bool, true),
                col("t \"x\"", Kind::Text, true),
                col("y", Kind::Bytes, true),
                col("i", Kind::Int, true),
            ],
            kl: Nat::from(1_u64),
        }]
    }

    fn load(rows: Vec<Table>) -> Option<Table> {
        rows.into_iter().next()
    }

    fn writes(ws: &Table) -> Vec<Write> {
        ws.iter()
            .map(|row| Write::Put {
                table: Nat::from(0_u64),
                key_len: Nat::from(1_u64),
                row: row.clone(),
            })
            .collect()
    }

    fn encode_reply(_: &Table) -> Vec<u8> {
        Vec::new()
    }

    fn decode_reply(_: &[u8]) -> Option<Table> {
        None
    }
}

fn int(v: i64) -> Val {
    Val::Int { v }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn every_kind_reads_back_as_written() {
    let url = cluster().locked::<Rows>("values_kinds").await;
    let none = Config {
        cache_tenants: 0,
        ..Config::default()
    };
    let pg = PgEngine::<Rows>::connect(&url, 2, none)
        .await
        .expect("the engine connects");
    let rows = vec![
        vec![
            int(i64::MIN),
            Val::Bool { v: true },
            Val::Text { v: String::new() },
            Val::Bytes { v: Vec::new() },
            int(i64::MAX),
        ],
        vec![
            int(-1),
            Val::Bool { v: false },
            Val::Text {
                v: "\"quoted\" 'single' \\ é 日本 🦀 \u{7f}".to_owned(),
            },
            Val::Bytes {
                v: (0..=255).collect(),
            },
            int(0),
        ],
        vec![int(0), Val::Null, Val::Null, Val::Null, Val::Null],
        vec![
            int(i64::MAX),
            Val::Bool { v: true },
            Val::Text {
                v: "x".repeat(10_000),
            },
            Val::Bytes { v: vec![0] },
            Val::Null,
        ],
    ];
    for row in &rows {
        let r = pg.execute(1, Cmd::Put(row.clone()), None).await;
        assert_eq!(r, Ok(Ok(Vec::new())));
    }
    let replaced = vec![
        int(-1),
        Val::Null,
        Val::Text {
            v: "new".to_owned(),
        },
        Val::Null,
        int(7),
    ];
    pg.execute(1, Cmd::Put(replaced.clone()), None)
        .await
        .unwrap()
        .unwrap();
    let mut expected = rows.clone();
    expected[1] = replaced;
    let read = pg.execute(1, Cmd::Read, None).await.unwrap().unwrap();
    let key = |r: &Vec<Val>| match r[0] {
        Val::Int { v } => v,
        _ => panic!("an integer key"),
    };
    let (mut read, mut expected) = (read, expected);
    read.sort_by_key(key);
    expected.sort_by_key(key);
    assert_eq!(read, expected);
    assert_eq!(
        pg.execute(2, Cmd::Read, None).await,
        Ok(Ok(Vec::new())),
        "another tenant"
    );

    let nul = vec![
        int(5),
        Val::Null,
        Val::Text {
            v: "a\0b".to_owned(),
        },
        Val::Null,
        Val::Null,
    ];
    let r = pg.execute(1, Cmd::Put(nul), None).await;
    assert!(matches!(r, Err(EngineError::Database(_))), "{r:?}");
    let read = pg.execute(1, Cmd::Read, None).await.unwrap().unwrap();
    assert_eq!(read.len(), 4, "nothing stored");
    let stats = pg.stats();
    let load = |a: &std::sync::atomic::AtomicU64| a.load(std::sync::atomic::Ordering::Relaxed);
    assert_eq!(
        load(&stats.loads),
        load(&stats.attempts),
        "every attempt read the rows"
    );
}
