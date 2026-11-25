//! The calculator on the PostgreSQL engine: the commands of one tenant leave the rows of the
//! others as they were, and the server started again on the same database answers from the
//! state the first one stored.

use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use leanharbor::Engine;
use leanharbor_calculator::{Calculator, kernel};
use leanharbor_pg::testing::{ENGINE_ROLE, OWNER, cluster, connect};
use leanharbor_pg::{Config, PgEngine};

const COMMANDS: &str = include_str!("../../../testdata/calculator-commands.txt");
const SECRET: &str = "secret";

fn parse(line: &str) -> (kernel::Principal, kernel::Command) {
    let words: Vec<&str> = line.split(' ').collect();
    let number = |s: &str| s.parse::<u64>().expect("a number");
    let actor = kernel::Principal {
        org: number(words[0]),
        user: number(words[1]),
    };
    let cmd = match words[2..] {
        ["set", n] => kernel::Command::Set { value: number(n) },
        ["apply", op, n] => kernel::Command::Apply {
            op: match op {
                "add" => kernel::Op::Add,
                "sub" => kernel::Op::Sub,
                "mul" => kernel::Op::Mul,
                "div" => kernel::Op::Div,
                other => panic!("unknown op {other}"),
            },
            arg: number(n),
        },
        ["get"] => kernel::Command::Get,
        _ => panic!("bad line {line}"),
    };
    (actor, cmd)
}

type Rows = BTreeMap<(i64, i64), i64>;

async fn rows(admin: &tokio_postgres::Client) -> Rows {
    admin
        .query("SELECT tenant_id, \"user\", value FROM memories", &[])
        .await
        .unwrap()
        .iter()
        .map(|r| ((r.get(0), r.get(1)), r.get(2)))
        .collect()
}

/// The command list mixes three tenants. After each command, every row of the other tenants,
/// and of the other users of its tenant, is as it was.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn tenants_leave_each_other_rows() {
    let name = "calculator_isolation";
    let url = cluster().locked::<Calculator>(name).await;
    let admin = connect(&cluster().admin_url(name)).await;
    let engine = PgEngine::<Calculator>::connect(&url, 2, Config::default())
        .await
        .expect("the engine connects");
    let mut before = rows(&admin).await;
    let mut tenants = std::collections::BTreeSet::new();
    for line in COMMANDS.lines() {
        let (actor, cmd) = parse(line);
        tenants.insert(actor.org);
        let mine = (actor.org as i64, actor.user as i64);
        let _ = engine
            .execute(actor, cmd, None)
            .await
            .expect("no engine error");
        let after = rows(&admin).await;
        let others = |r: &Rows| -> Rows {
            r.iter()
                .filter(|(k, _)| **k != mine)
                .map(|(k, v)| (*k, *v))
                .collect()
        };
        assert_eq!(others(&after), others(&before), "{line}");
        before = after;
    }
    assert_eq!(tenants.len(), 3);
    let stored: std::collections::BTreeSet<i64> = before.keys().map(|(t, _)| *t).collect();
    assert_eq!(stored.len(), 3);
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
    let child = Command::new(env!("CARGO_BIN_EXE_leanharbor-calculator"))
        .env("LEANHARBOR_SECRET", SECRET)
        .env("LEANHARBOR_LISTEN", &addr)
        .env("LEANHARBOR_DATABASE_URL", url)
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
    let out = Command::new(env!("CARGO_BIN_EXE_leanharbor-calculator"))
        .env("LEANHARBOR_SECRET", SECRET)
        .env("LEANHARBOR_ISSUE", format!("{tenant}:{user}"))
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

/// `LEANHARBOR_LOCKDOWN` with the administrator's connection string makes the tables, and
/// the server then runs as the engine's role.
fn lockdown(name: &str) {
    let status = Command::new(env!("CARGO_BIN_EXE_leanharbor-calculator"))
        .env("LEANHARBOR_SECRET", SECRET)
        .env("LEANHARBOR_DATABASE_URL", cluster().admin_url(name))
        .env("LEANHARBOR_LOCKDOWN", format!("{OWNER}:{ENGINE_ROLE}"))
        .status()
        .expect("the lockdown runs");
    assert!(status.success());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn state_survives_a_restart_of_the_server() {
    let name = "calculator_restart";
    let url = cluster().database(name).await;
    lockdown(name);
    let (a, b) = (token(1, 7), token(2, 7));
    let first = start(&url);
    assert_eq!(
        post(&first, &a, r#"{"cmd":"set","value":6}"#),
        (200, r#"{"value":6}"#.to_owned())
    );
    assert_eq!(
        post(&first, &a, r#"{"cmd":"apply","op":"mul","arg":7}"#),
        (200, r#"{"value":42}"#.to_owned())
    );
    assert_eq!(
        post(&first, &a, r#"{"cmd":"apply","op":"div","arg":0}"#),
        (422, r#"{"error":"division_by_zero"}"#.to_owned())
    );
    assert_eq!(
        post(&first, &b, r#"{"cmd":"set","value":5}"#),
        (200, r#"{"value":5}"#.to_owned())
    );
    drop(first);
    let second = start(&url);
    assert_eq!(
        post(&second, &a, r#"{"cmd":"get"}"#),
        (200, r#"{"value":42}"#.to_owned())
    );
    assert_eq!(
        post(&second, &b, r#"{"cmd":"get"}"#),
        (200, r#"{"value":5}"#.to_owned())
    );
    assert_eq!(
        post(&second, &token(1, 8), r#"{"cmd":"get"}"#),
        (200, r#"{"value":0}"#.to_owned())
    );
    let admin = connect(&cluster().admin_url(name)).await;
    let owner: String = admin
        .query_one(
            "SELECT tableowner FROM pg_tables WHERE tablename = 'memories'",
            &[],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(owner, OWNER);
}
