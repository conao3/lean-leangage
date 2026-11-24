//! The generated Rust behind the memory engine against the kernel run natively by Lean
//! (`calculator-oracle`), on the shared command list.

use std::io::Write;
use std::process::{Command, Stdio};

use leanharbor::Engine;
use leanharbor::memory::MemoryEngine;
use leanharbor_calculator::{Calculator, kernel};

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

#[tokio::test]
async fn generated_rust_agrees_with_lean() {
    let engine = MemoryEngine::<Calculator>::new();
    let mut ours = String::new();
    for line in COMMANDS.lines() {
        let (actor, cmd) = parse(line);
        let executed = engine.execute(actor, cmd, None).await;
        match executed.expect("no engine error") {
            Ok(reply) => ours.push_str(&format!("ok {}\n", reply.v)),
            Err(kernel::Error::Overflow) => ours.push_str("error overflow\n"),
            Err(kernel::Error::Underflow) => ours.push_str("error underflow\n"),
            Err(kernel::Error::DivByZero) => ours.push_str("error division_by_zero\n"),
        }
    }
    let theirs = oracle();
    assert_eq!(ours.lines().count(), 5000);
    for (i, (a, b)) in ours.lines().zip(theirs.lines()).enumerate() {
        assert_eq!(a, b, "line {}: {}", i + 1, COMMANDS.lines().nth(i).unwrap());
    }
    assert_eq!(ours, theirs);
}
