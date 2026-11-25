//! The generated Rust behind the memory engine and behind the PostgreSQL engine against the
//! kernel run natively by Lean (`calculator-oracle`), on the shared command list.

use std::io::Write;
use std::process::{Command, Stdio};

use leanharbor::memory::MemoryEngine;
use leanharbor::{Engine, Executed};
use leanharbor_calculator::{Calculator, kernel};
use leanharbor_pg::testing::cluster;
use leanharbor_pg::{Config, PgEngine};

const COMMANDS: &str = include_str!("../../../testdata/calculator-commands.txt");

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

fn oracle() -> String {
    let path = std::env::var("LEANHARBOR_CALCULATOR_ORACLE")
        .expect("LEANHARBOR_CALCULATOR_ORACLE is required");
    let mut child = Command::new(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("the oracle starts");
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let writer = std::thread::spawn(move || stdin.write_all(COMMANDS.as_bytes()));
    let output = child.wait_with_output().expect("the oracle runs");
    writer
        .join()
        .expect("writer")
        .expect("commands are written");
    assert!(output.status.success());
    String::from_utf8(output.stdout).expect("utf-8")
}

fn line(executed: Executed<Calculator>) -> String {
    match executed.expect("no engine error") {
        Ok(reply) => format!("ok {}\n", reply.v),
        Err(kernel::Error::Overflow) => "error overflow\n".to_owned(),
        Err(kernel::Error::Underflow) => "error underflow\n".to_owned(),
        Err(kernel::Error::DivByZero) => "error division_by_zero\n".to_owned(),
    }
}

async fn run(engine: &impl Engine<Calculator>) -> String {
    let mut out = String::new();
    for line_ in COMMANDS.lines() {
        let (actor, cmd) = parse(line_);
        out.push_str(&line(engine.execute(actor, cmd, None).await));
    }
    out
}

fn agree(ours: &str, theirs: &str) {
    assert_eq!(ours.lines().count(), 5000);
    for (i, (a, b)) in ours.lines().zip(theirs.lines()).enumerate() {
        assert_eq!(a, b, "line {}: {}", i + 1, COMMANDS.lines().nth(i).unwrap());
    }
    assert_eq!(ours, theirs);
}

#[tokio::test]
async fn generated_rust_agrees_with_lean() {
    let ours = run(&MemoryEngine::<Calculator>::new()).await;
    agree(&ours, &oracle());
}

/// The rows stored and read back in PostgreSQL give every command the reply the memory engine
/// and Lean give it: PostgreSQL runs the generated statements as the model of `Leanharbor.Sql`
/// says. The engine that remembers no snapshot reads the rows back for every command; the one
/// that remembers them gives the same replies.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn postgres_engine_agrees_with_memory_engine_and_lean() {
    let memory = run(&MemoryEngine::<Calculator>::new()).await;
    let lean = oracle();
    for (name, cache_tenants) in [
        ("calculator_differential", 0),
        ("calculator_differential_cached", 1024),
    ] {
        let url = cluster().locked::<Calculator>(name).await;
        let config = Config {
            cache_tenants,
            ..Config::default()
        };
        let engine = PgEngine::<Calculator>::connect(&url, 2, config)
            .await
            .expect("the engine connects");
        let ours = run(&engine).await;
        agree(&ours, &memory);
        agree(&ours, &lean);
        let stats = engine.stats();
        let load = |a: &std::sync::atomic::AtomicU64| a.load(std::sync::atomic::Ordering::Relaxed);
        assert_eq!(load(&stats.retries), 0);
        if cache_tenants == 0 {
            assert_eq!(
                load(&stats.loads),
                load(&stats.attempts),
                "every attempt read the rows"
            );
        }
    }
}
