//! The generated Rust JSON reader, the functions on requests and responses and the calculator's
//! functions on the wire against those run natively by Lean (`request-oracle`), on the shared
//! lines. The line format is described in `lean/RequestOracle.lean`. A text to read that is
//! UTF-8 is also read by `read_string`, which must read what `read` reads, and its acceptance is
//! compared with serde_json's. A fingerprint is compared with the `Debug` form of the command and
//! a scope with `u<user>`, the bytes the rows of `leangage_idempotency` hold.

use std::io::Write as _;
use std::process::{Command, Stdio};

use leangage::http_format::{self, Body, Failure, Response};
use leangage::json_read::{self, Item};
use leangage_calculator::{kernel, wire};
use serde::de::IgnoredAny;

const CASES: &str = include_str!("../../../testdata/request-cases.txt");

fn bytes(word: &str) -> Vec<u8> {
    let hex = word.strip_prefix('x').expect("bytes start with x");
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect()
}

fn text(word: &str) -> String {
    String::from_utf8(bytes(word)).expect("the line holds UTF-8")
}

fn show(bytes: &[u8]) -> String {
    let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("x{hex}")
}

fn number(word: &str) -> u64 {
    word.parse().expect("a u64")
}

fn show_item(item: &Item) -> String {
    match item {
        Item::Null => "n".to_owned(),
        Item::Bool { b: true } => "t".to_owned(),
        Item::Bool { b: false } => "f".to_owned(),
        Item::Num { n } => format!("u{n}"),
        Item::Number => "#".to_owned(),
        Item::Str { s } => format!("s{}", show(s)),
        Item::Key { s } => format!("k{}", show(s)),
        Item::ArrOpen => "[".to_owned(),
        Item::ArrClose => "]".to_owned(),
        Item::ObjOpen => "{".to_owned(),
        Item::ObjClose => "}".to_owned(),
    }
}

fn show_response(head: &str, r: &Response) -> String {
    format!("{head} {} {}", r.status, show(&r.body))
}

fn op(word: &str) -> kernel::Op {
    match word {
        "add" => kernel::Op::Add,
        "sub" => kernel::Op::Sub,
        "mul" => kernel::Op::Mul,
        "div" => kernel::Op::Div,
        _ => panic!("bad operation {word}"),
    }
}

fn command(words: &[&str]) -> kernel::Command {
    match words {
        ["set", n] => kernel::Command::Set { value: number(n) },
        ["apply", o, n] => kernel::Command::Apply {
            op: op(o),
            arg: number(n),
        },
        ["get"] => kernel::Command::Get,
        _ => panic!("bad command {words:?}"),
    }
}

fn show_command(cmd: &kernel::Command) -> String {
    match cmd {
        kernel::Command::Set { value } => format!("set {value}"),
        kernel::Command::Apply { op, arg } => {
            let name = match op {
                kernel::Op::Add => "add",
                kernel::Op::Sub => "sub",
                kernel::Op::Mul => "mul",
                kernel::Op::Div => "div",
            };
            format!("apply {name} {arg}")
        }
        kernel::Command::Get => "get".to_owned(),
    }
}

fn body(word: &str) -> Body {
    match word {
        "notutf8" => Body::NotUtf8,
        "toolarge" => Body::TooLarge,
        "unreadable" => Body::Unreadable,
        _ => Body::Text { s: text(word) },
    }
}

fn failure(word: &str) -> Failure {
    match word {
        "bad_signature" => Failure::BadSignature,
        "conflict" => Failure::Conflict,
        "stopped" => Failure::Stopped,
        "retries_exhausted" => Failure::RetriesExhausted,
        "database" => Failure::Database,
        "commit_unknown" => Failure::CommitUnknown,
        "broken" => Failure::Broken,
        _ => panic!("bad failure {word}"),
    }
}

fn show_auth(result: Result<http_format::Bearer, Response>) -> String {
    match result {
        Ok(b) => format!(
            "ok {} {} {} {} {}",
            b.tenant,
            b.user,
            b.exp,
            show(&b.payload),
            show(&b.sig)
        ),
        Err(r) => show_response("err", &r),
    }
}

/// Whether the text is one the reader refuses although it is in the grammar of RFC 8259: it
/// holds the escape of a surrogate.
fn has_surrogate_escape(text: &str) -> bool {
    let lower = text.to_ascii_lowercase();
    [
        "\\ud8", "\\ud9", "\\uda", "\\udb", "\\udc", "\\udd", "\\ude", "\\udf",
    ]
    .iter()
    .any(|escape| lower.contains(escape))
}

struct Counts {
    utf8: usize,
    compared: usize,
}

fn run(line: &str, counts: &mut Counts) -> String {
    let words: Vec<&str> = line.split(' ').collect();
    match words.as_slice() {
        ["read", b] => {
            let input = bytes(b);
            let items = json_read::read(input.clone());
            if let Ok(text) = std::str::from_utf8(&input) {
                counts.utf8 += 1;
                assert_eq!(json_read::read_string(text), items, "read_string of {line}");
                if !has_surrogate_escape(text) {
                    counts.compared += 1;
                    let serde = serde_json::from_str::<IgnoredAny>(text).is_ok();
                    assert_eq!(items.is_some(), serde, "serde_json on {line}");
                }
            }
            match items {
                Some(items) => {
                    let mut out = vec!["items".to_owned()];
                    out.extend(items.iter().map(show_item));
                    out.join(" ")
                }
                None => "none".to_owned(),
            }
        }
        ["auth", "-"] => show_auth(http_format::authenticate(None)),
        ["auth", h] => show_auth(http_format::authenticate(Some(text(h)))),
        ["request", tenant, user, exp, now, b] => {
            match wire::request(
                number(tenant),
                number(user),
                number(exp),
                number(now),
                body(b),
            ) {
                Ok(call) => format!(
                    "ok {} {} {}",
                    call.actor.org,
                    call.actor.user,
                    show_command(&call.cmd)
                ),
                Err(r) => show_response("err", &r),
            }
        }
        ["respond", "ok", v] => {
            show_response("resp", &wire::respond(Ok(kernel::Reply { v: number(v) })))
        }
        ["respond", "err", name] => {
            let refusal = match *name {
                "overflow" => kernel::Error::Overflow,
                "underflow" => kernel::Error::Underflow,
                "division_by_zero" => kernel::Error::DivByZero,
                _ => panic!("bad refusal {name}"),
            };
            show_response("resp", &wire::respond(Err(refusal)))
        }
        ["failure", name] => show_response("resp", &http_format::failed(failure(name))),
        ["fingerprint", cmd @ ..] => {
            let cmd = command(cmd);
            let bytes = wire::fingerprint(cmd.clone());
            assert_eq!(bytes, format!("{cmd:?}").into_bytes(), "the stored form");
            format!("bytes {}", show(&bytes))
        }
        ["scope", user] => {
            let actor = kernel::Principal {
                org: 0,
                user: number(user),
            };
            let scope = wire::scope(actor);
            assert_eq!(scope, format!("u{user}"), "the stored form");
            format!("text {}", show(scope.as_bytes()))
        }
        _ => panic!("bad line {line}"),
    }
}

fn oracle() -> String {
    let path =
        std::env::var("LEANGAGE_REQUEST_ORACLE").expect("LEANGAGE_REQUEST_ORACLE is required");
    let mut child = Command::new(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("the oracle starts");
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let writer = std::thread::spawn(move || stdin.write_all(CASES.as_bytes()));
    let output = child.wait_with_output().expect("the oracle runs");
    writer.join().expect("writer").expect("cases are written");
    assert!(output.status.success());
    String::from_utf8(output.stdout).expect("utf-8")
}

#[test]
fn generated_rust_request_functions_agree_with_lean() {
    let mut counts = Counts {
        utf8: 0,
        compared: 0,
    };
    let ours: Vec<String> = CASES.lines().map(|line| run(line, &mut counts)).collect();
    let theirs = oracle();
    assert_eq!(ours.len(), theirs.lines().count());
    assert!(counts.utf8 > 800, "{} texts are UTF-8", counts.utf8);
    assert!(counts.compared > 700, "{} texts compared", counts.compared);
    for (i, (a, b)) in ours.iter().zip(theirs.lines()).enumerate() {
        assert_eq!(a, b, "line {}: {}", i + 1, CASES.lines().nth(i).unwrap());
    }
}
