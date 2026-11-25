//! The generated Rust behind the memory engine and behind the PostgreSQL engine against the
//! kernel run natively by Lean (`notes-oracle`), on the shared command list.

use std::io::Write;
use std::process::{Command, Stdio};

use leanharbor::memory::MemoryEngine;
use leanharbor::{Engine, Executed};
use leanharbor_notes::{Notes, kernel, refusal_name};
use leanharbor_pg::testing::cluster;
use leanharbor_pg::{Config, PgEngine};

const COMMANDS: &str = include_str!("../../../testdata/notes-commands.txt");

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

fn flag(b: bool) -> &'static str {
    if b { "1" } else { "0" }
}

fn note(n: &kernel::Note) -> String {
    format!("{}:{}:{}:{}", n.id, n.owner, flag(n.shared), n.body)
}

fn show(reply: &kernel::Reply) -> String {
    match reply {
        kernel::Reply::Done => "done".to_owned(),
        kernel::Reply::Found { n } => format!("found {}", note(n)),
        kernel::Reply::Notes { ns } => std::iter::once(format!("notes {}", ns.len()))
            .chain(ns.iter().map(note))
            .collect::<Vec<_>>()
            .join(" "),
        kernel::Reply::Members { ms } => std::iter::once(format!("members {}", ms.len()))
            .chain(ms.iter().map(|m| format!("{}:{}", m.user, flag(m.admin))))
            .collect::<Vec<_>>()
            .join(" "),
    }
}

fn oracle() -> String {
    let path =
        std::env::var("LEANHARBOR_NOTES_ORACLE").expect("LEANHARBOR_NOTES_ORACLE is required");
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

fn line(executed: Executed<Notes>) -> String {
    match executed.expect("no engine error") {
        Ok(reply) => format!("ok {}\n", show(&reply)),
        Err(refusal) => format!("error {}\n", refusal_name(&refusal)),
    }
}

async fn run(engine: &impl Engine<Notes>) -> String {
    let mut out = String::new();
    for line_ in COMMANDS.lines() {
        let (actor, cmd) = parse(line_);
        out.push_str(&line(engine.execute(actor, cmd, None).await));
    }
    out
}

fn agree(ours: &str, theirs: &str) {
    assert_eq!(ours.lines().count(), 3000);
    for (i, (a, b)) in ours.lines().zip(theirs.lines()).enumerate() {
        assert_eq!(a, b, "line {}: {}", i + 1, COMMANDS.lines().nth(i).unwrap());
    }
    assert_eq!(ours, theirs);
}

#[tokio::test]
async fn generated_rust_agrees_with_lean() {
    let ours = run(&MemoryEngine::<Notes>::new()).await;
    agree(&ours, &oracle());
}

/// The rows stored and read back in PostgreSQL give every command the reply the memory engine
/// and Lean give it, listings and refusals of the guard included.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn postgres_engine_agrees_with_memory_engine_and_lean() {
    let url = cluster().locked::<Notes>("notes_differential").await;
    let engine = PgEngine::<Notes>::connect(&url, 2, Config::default())
        .await
        .expect("the engine connects");
    let ours = run(&engine).await;
    agree(&ours, &run(&MemoryEngine::<Notes>::new()).await);
    agree(&ours, &oracle());
    assert_eq!(
        engine
            .stats()
            .retries
            .load(std::sync::atomic::Ordering::Relaxed),
        0
    );
}
