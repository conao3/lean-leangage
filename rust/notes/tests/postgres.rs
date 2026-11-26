//! The notes on the PostgreSQL engine: a refused command, the guard's denials included, writes no
//! row; a command of one tenant leaves the rows of the others as they were; the stored replies of
//! keyed requests read back; and the server started again on the same database answers from the
//! state the first one stored.

use std::collections::BTreeSet;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use leangage::memory::MemoryEngine;
use leangage::{Engine, Idempotency, Storage};
use leangage_notes::{Notes, Refusal, kernel};
use leangage_pg::testing::{ENGINE_ROLE, OWNER, cluster, connect};
use leangage_pg::{Config, PgEngine};

const COMMANDS: &str = include_str!("../../../testdata/notes-commands.txt");
const SECRET: &str = "secret";

fn parse(line: &str) -> (kernel::Principal, kernel::Command) {
    let words: Vec<&str> = line.split(' ').collect();
    let number = |s: &str| s.parse::<u64>().expect("a number");
    let flag = |s: &str| match s {
        "0" => false,
        "1" => true,
        other => panic!("bad flag {other}"),
    };
    let actor = kernel::Principal {
        org: number(words[0]),
        user: number(words[1]),
    };
    let cmd = match words[2..] {
        ["add-member", user, admin] => kernel::Command::AddMember {
            user: number(user),
            admin: flag(admin),
        },
        ["remove-member", user] => kernel::Command::RemoveMember { user: number(user) },
        ["put-note", id, shared, body] => kernel::Command::PutNote {
            id: number(id),
            body: body.to_owned(),
            shared: flag(shared),
        },
        ["delete-note", id] => kernel::Command::DeleteNote { id: number(id) },
        ["read-note", id] => kernel::Command::ReadNote { id: number(id) },
        ["list-notes"] => kernel::Command::ListNotes,
        ["list-members"] => kernel::Command::ListMembers,
        _ => panic!("bad line {line}"),
    };
    (actor, cmd)
}

/// Every row of both tables, with its tenant.
#[derive(Debug, PartialEq, Eq)]
struct Rows {
    members: BTreeSet<(i64, i64, bool)>,
    notes: BTreeSet<(i64, i64, i64, bool, String)>,
}

impl Rows {
    fn of(&self, tenant: i64) -> Rows {
        Rows {
            members: self
                .members
                .iter()
                .filter(|r| r.0 == tenant)
                .cloned()
                .collect(),
            notes: self
                .notes
                .iter()
                .filter(|r| r.0 == tenant)
                .cloned()
                .collect(),
        }
    }

    fn others(&self, tenant: i64) -> Rows {
        Rows {
            members: self
                .members
                .iter()
                .filter(|r| r.0 != tenant)
                .cloned()
                .collect(),
            notes: self
                .notes
                .iter()
                .filter(|r| r.0 != tenant)
                .cloned()
                .collect(),
        }
    }
}

async fn rows(admin: &tokio_postgres::Client) -> Rows {
    let members = admin
        .query("SELECT tenant_id, \"user\", admin FROM members", &[])
        .await
        .unwrap()
        .iter()
        .map(|r| (r.get(0), r.get(1), r.get(2)))
        .collect();
    let notes = admin
        .query("SELECT tenant_id, id, owner, shared, body FROM notes", &[])
        .await
        .unwrap()
        .iter()
        .map(|r| (r.get(0), r.get(1), r.get(2), r.get(3), r.get(4)))
        .collect();
    Rows { members, notes }
}

/// Along the command list, which mixes two tenants, a refused command leaves every row as it
/// was, and an accepted one leaves the rows of the other tenant as they were. A read-only command
/// writes no row either.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn refusals_write_no_row() {
    let name = "notes_refusals";
    let url = cluster().locked::<Notes>(name).await;
    let admin = connect(&cluster().admin_url(name)).await;
    let engine = PgEngine::<Notes>::connect(&url, 2, Config::default())
        .await
        .expect("the engine connects");
    let mut before = rows(&admin).await;
    let (mut denied, mut refused, mut read_only) = (0, 0, 0);
    let mut tenants = BTreeSet::new();
    for line in COMMANDS.lines() {
        let (actor, cmd) = parse(line);
        let tenant = actor.org as i64;
        tenants.insert(tenant);
        let reads = kernel::read_only(cmd.clone());
        let outcome = engine
            .execute(actor, cmd, None)
            .await
            .expect("no engine error");
        let after = rows(&admin).await;
        match outcome {
            Err(refusal) => {
                assert_eq!(after, before, "{line}");
                refused += 1;
                if refusal == Refusal::Denied {
                    denied += 1;
                }
            }
            Ok(_) if reads => {
                assert_eq!(after, before, "{line}");
                read_only += 1;
            }
            Ok(_) => assert_eq!(after.others(tenant), before.others(tenant), "{line}"),
        }
        before = after;
    }
    assert_eq!(tenants.len(), 2);
    assert!(tenants.iter().all(|t| !before.of(*t).notes.is_empty()));
    assert_eq!((denied, refused, read_only), (1383, 1826, 849));
}

/// A body holding NUL, which PostgreSQL cannot store in `TEXT`, is refused by the kernel on both
/// engines and writes no row.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_body_with_nul_is_refused() {
    let name = "notes_nul";
    let url = cluster().locked::<Notes>(name).await;
    let admin = connect(&cluster().admin_url(name)).await;
    let engine = PgEngine::<Notes>::connect(&url, 2, Config::default())
        .await
        .expect("the engine connects");
    let memory = MemoryEngine::<Notes>::new();
    let actor = kernel::Principal { org: 1, user: 1 };
    let first = kernel::Command::AddMember {
        user: 1,
        admin: true,
    };
    let nul = kernel::Command::PutNote {
        id: 1,
        body: "a\0b".to_owned(),
        shared: true,
    };
    for cmd in [first, nul.clone()] {
        let pg = engine.execute(actor.clone(), cmd.clone(), None).await;
        assert_eq!(pg, memory.execute(actor.clone(), cmd, None).await);
    }
    assert_eq!(
        engine.execute(actor.clone(), nul, None).await,
        Ok(Err(Refusal::App {
            e: kernel::Error::BadText
        }))
    );
    assert_eq!(
        engine
            .execute(actor, kernel::Command::ReadNote { id: 1 }, None)
            .await,
        Ok(Err(Refusal::App {
            e: kernel::Error::NotFound
        }))
    );
    assert!(rows(&admin).await.notes.is_empty());
}

/// The stored form of every reply of the command list reads back as the reply, and a repeated
/// keyed request gets the stored reply.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn stored_replies_read_back() {
    let memory = MemoryEngine::<Notes>::new();
    let mut replies = 0;
    for line in COMMANDS.lines() {
        let (actor, cmd) = parse(line);
        if let Ok(Ok(reply)) = memory.execute(actor, cmd, None).await {
            let bytes = <Notes as Storage>::encode_reply(&reply);
            assert_eq!(
                <Notes as Storage>::decode_reply(&bytes),
                Some(reply),
                "{line}"
            );
            replies += 1;
        }
    }
    assert_eq!(replies, 1174);
    let url = cluster().locked::<Notes>("notes_replies").await;
    let engine = PgEngine::<Notes>::connect(&url, 2, Config::default())
        .await
        .expect("the engine connects");
    let actor = kernel::Principal { org: 1, user: 1 };
    let idem = |key: &str, cmd: &kernel::Command| Idempotency {
        scope: "u1".to_owned(),
        key: key.to_owned(),
        fingerprint: format!("{cmd:?}").into_bytes(),
    };
    let setup = [
        kernel::Command::AddMember {
            user: 1,
            admin: true,
        },
        kernel::Command::PutNote {
            id: 2,
            body: "\"quoted\" \\ ノート".to_owned(),
            shared: false,
        },
        kernel::Command::PutNote {
            id: 1,
            body: "first".to_owned(),
            shared: true,
        },
    ];
    for cmd in setup {
        engine
            .execute(actor.clone(), cmd, None)
            .await
            .unwrap()
            .unwrap();
    }
    let list = kernel::Command::ListNotes;
    let first = engine
        .execute(actor.clone(), list.clone(), Some(idem("k", &list)))
        .await;
    engine
        .execute(actor.clone(), kernel::Command::DeleteNote { id: 1 }, None)
        .await
        .unwrap()
        .unwrap();
    let second = engine
        .execute(actor.clone(), list.clone(), Some(idem("k", &list)))
        .await;
    assert_eq!(first, second);
    let Ok(Ok(kernel::Reply::Notes { ns })) = first else {
        panic!("a listing: {first:?}")
    };
    assert_eq!(ns.iter().map(|n| n.id).collect::<Vec<_>>(), vec![1, 2]);
    assert_eq!(
        engine
            .stats()
            .replays
            .load(std::sync::atomic::Ordering::Relaxed),
        1
    );
}

struct Server {
    child: Child,
    addr: String,
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port()
}

fn start(url: &str) -> Server {
    let addr = format!("127.0.0.1:{}", free_port());
    let child = Command::new(env!("CARGO_BIN_EXE_leangage-notes"))
        .env("LEANGAGE_SECRET", SECRET)
        .env("LEANGAGE_LISTEN", &addr)
        .env("LEANGAGE_DATABASE_URL", url)
        .spawn()
        .expect("the server starts");
    let server = Server { child, addr };
    let start = Instant::now();
    while TcpStream::connect(&server.addr).is_err() {
        assert!(
            start.elapsed() < Duration::from_secs(20),
            "the server listens"
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    server
}

fn token(tenant: u64, user: u64) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_leangage-notes"))
        .env("LEANGAGE_SECRET", SECRET)
        .env("LEANGAGE_ISSUE", format!("{tenant}:{user}"))
        .output()
        .expect("the server issues a token");
    String::from_utf8(out.stdout).unwrap().trim().to_owned()
}

/// `POST /rpc` over one connection: the status and the body.
fn post(server: &Server, token: &str, body: &str) -> (u16, String) {
    let mut stream = TcpStream::connect(&server.addr).unwrap();
    write!(
        stream,
        "POST /rpc HTTP/1.1\r\nHost: {}\r\nAuthorization: Bearer {token}\r\n\
         Content-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
        server.addr,
        body.len()
    )
    .unwrap();
    let mut response = String::new();
    stream.read_to_string(&mut response).unwrap();
    let status = response[9..12].parse().unwrap();
    let body = response.split("\r\n\r\n").nth(1).unwrap_or("").to_owned();
    (status, body)
}

/// `LEANGAGE_LOCKDOWN` with the administrator's connection string makes the tables, and
/// the server then runs as the engine's role.
fn lockdown(name: &str) {
    let status = Command::new(env!("CARGO_BIN_EXE_leangage-notes"))
        .env("LEANGAGE_SECRET", SECRET)
        .env("LEANGAGE_DATABASE_URL", cluster().admin_url(name))
        .env("LEANGAGE_LOCKDOWN", format!("{OWNER}:{ENGINE_ROLE}"))
        .status()
        .expect("the lockdown runs");
    assert!(status.success());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn state_survives_a_restart_of_the_server() {
    let name = "notes_restart";
    let url = cluster().database(name).await;
    lockdown(name);
    let (admin, member, other_org) = (token(1, 1), token(1, 2), token(2, 1));
    let first = start(&url);
    for (who, body, reply) in [
        (
            &admin,
            r#"{"cmd":"add_member","user":1,"admin":true}"#,
            (200, r#"{"done":true}"#),
        ),
        (
            &admin,
            r#"{"cmd":"add_member","user":2,"admin":false}"#,
            (200, r#"{"done":true}"#),
        ),
        (
            &admin,
            r#"{"cmd":"put_note","id":9,"body":"draft","shared":false}"#,
            (200, r#"{"done":true}"#),
        ),
        (
            &member,
            r#"{"cmd":"put_note","id":3,"body":"mine","shared":true}"#,
            (200, r#"{"done":true}"#),
        ),
        (
            &member,
            r#"{"cmd":"put_note","id":9,"body":"taken","shared":true}"#,
            (403, r#"{"error":"denied"}"#),
        ),
        (
            &other_org,
            r#"{"cmd":"add_member","user":1,"admin":false}"#,
            (200, r#"{"done":true}"#),
        ),
    ] {
        assert_eq!(
            post(&first, who, body),
            (reply.0, reply.1.to_owned()),
            "{body}"
        );
    }
    drop(first);
    let second = start(&url);
    assert_eq!(
        post(&second, &admin, r#"{"cmd":"list_notes"}"#),
        (
            200,
            r#"{"notes":[{"body":"mine","id":3,"owner":2,"shared":true},{"body":"draft","id":9,"owner":1,"shared":false}]}"#
                .to_owned()
        )
    );
    assert_eq!(
        post(&second, &member, r#"{"cmd":"read_note","id":9}"#),
        (404, r#"{"error":"not_found"}"#.to_owned())
    );
    assert_eq!(
        post(&second, &member, r#"{"cmd":"list_members"}"#),
        (200, r#"{"members":[{"admin":false,"user":2}]}"#.to_owned())
    );
    assert_eq!(
        post(&second, &other_org, r#"{"cmd":"list_members"}"#),
        (200, r#"{"members":[{"admin":false,"user":1}]}"#.to_owned())
    );
    let admin_db = connect(&cluster().admin_url(name)).await;
    for table in ["members", "notes"] {
        let owner: String = admin_db
            .query_one(
                "SELECT tableowner FROM pg_tables WHERE tablename = $1",
                &[&table],
            )
            .await
            .unwrap()
            .get(0);
        assert_eq!(owner, OWNER);
    }
}
