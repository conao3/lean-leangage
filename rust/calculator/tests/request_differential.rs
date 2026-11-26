//! The tokens `json_text::lexemes` reads with serde_json, the generated functions on requests and
//! responses and the calculator's functions on the wire against those run natively by Lean
//! (`request-oracle`), on the shared lines. The line format is described in
//! `lean/RequestOracle.lean`. A fingerprint is compared with the `Debug` form of the command and
//! a scope with `u<user>`, the bytes the rows of `leangage_idempotency` hold.

use std::io::Write as _;
use std::process::{Command, Stdio};

use leangage::http::body_of;
use leangage::http_format::{self, Body, Failure, Response};
use leangage::json_lexemes::{self, Lexeme};
use leangage::json_text;
use leangage_calculator::{kernel, wire};

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

fn show_lexeme(lexeme: &Lexeme) -> String {
    match lexeme {
        Lexeme::Null => "n".to_owned(),
        Lexeme::Bool { b: true } => "t".to_owned(),
        Lexeme::Bool { b: false } => "f".to_owned(),
        Lexeme::Number { text } => match json_lexemes::number_of(text) {
            Some(n) => format!("u{n}"),
            None => "#".to_owned(),
        },
        Lexeme::Str { s } => format!("s{}", show(s.as_bytes())),
        Lexeme::Key { s } => format!("k{}", show(s.as_bytes())),
        Lexeme::ArrOpen => "[".to_owned(),
        Lexeme::ArrClose => "]".to_owned(),
        Lexeme::ObjOpen => "{".to_owned(),
        Lexeme::ObjClose => "}".to_owned(),
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
        "toolarge" => Body::TooLarge,
        "unreadable" => Body::Unreadable,
        _ => body_of(&bytes(word)),
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

#[derive(Default)]
struct Counts {
    texts: usize,
    read: usize,
}

fn run(line: &str, counts: &mut Counts) -> String {
    let words: Vec<&str> = line.split(' ').collect();
    match words.as_slice() {
        ["tokens", b] => {
            counts.texts += 1;
            match json_text::lexemes(&bytes(b)) {
                Some(lexemes) => {
                    counts.read += 1;
                    let mut out = vec!["tokens".to_owned()];
                    out.extend(lexemes.iter().map(show_lexeme));
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
    let mut counts = Counts::default();
    let ours: Vec<String> = CASES.lines().map(|line| run(line, &mut counts)).collect();
    let theirs = oracle();
    assert_eq!(ours.len(), theirs.lines().count());
    assert!(counts.texts > 1000, "{} texts", counts.texts);
    assert!(counts.read > 300, "{} texts read", counts.read);
    let wrong: Vec<String> = ours
        .iter()
        .zip(theirs.lines())
        .enumerate()
        .filter(|(_, (a, b))| a != b)
        .map(|(i, (a, b))| {
            let short = |s: &str| s.chars().take(60).collect::<String>();
            format!("line {}: ours {} theirs {}", i + 1, short(a), short(b))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
