//! The notes' generated Rust functions on the wire against those run natively by Lean
//! (`notes-request-oracle`), on the shared lines. The line format is described in
//! `lean/NotesRequestOracle.lean`. A fingerprint of a command without a body is compared with
//! the `Debug` form of the command and a scope with `u<user>`, the bytes the rows of
//! `leangage_idempotency` hold. The body of an accepted reply is compared with the same value
//! written by serde_json with its keys in order, and must be read back by `decode_reply`.

use std::io::Write as _;
use std::process::{Command, Stdio};

use leangage::http_format::{Body, Response};
use leangage_notes::{Refusal, kernel, wire};
use serde_json::{Value, json};

const CASES: &str = include_str!("../../../testdata/notes-request-cases.txt");

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

fn flag(word: &str) -> bool {
    match word {
        "t" => true,
        "f" => false,
        _ => panic!("bad flag {word}"),
    }
}

fn show_flag(flag: bool) -> &'static str {
    if flag { "t" } else { "f" }
}

fn show_response(head: &str, r: &Response) -> String {
    format!("{head} {} {}", r.status, show(&r.body))
}

fn command(words: &[&str]) -> kernel::Command {
    match words {
        ["add_member", user, admin] => kernel::Command::AddMember {
            user: number(user),
            admin: flag(admin),
        },
        ["remove_member", user] => kernel::Command::RemoveMember { user: number(user) },
        ["put_note", id, shared, body] => kernel::Command::PutNote {
            id: number(id),
            body: text(body),
            shared: flag(shared),
        },
        ["delete_note", id] => kernel::Command::DeleteNote { id: number(id) },
        ["read_note", id] => kernel::Command::ReadNote { id: number(id) },
        ["list_notes"] => kernel::Command::ListNotes,
        ["list_members"] => kernel::Command::ListMembers,
        _ => panic!("bad command {words:?}"),
    }
}

fn show_command(cmd: &kernel::Command) -> String {
    match cmd {
        kernel::Command::AddMember { user, admin } => {
            format!("add_member {user} {}", show_flag(*admin))
        }
        kernel::Command::RemoveMember { user } => format!("remove_member {user}"),
        kernel::Command::PutNote { id, body, shared } => format!(
            "put_note {id} {} {}",
            show_flag(*shared),
            show(body.as_bytes())
        ),
        kernel::Command::DeleteNote { id } => format!("delete_note {id}"),
        kernel::Command::ReadNote { id } => format!("read_note {id}"),
        kernel::Command::ListNotes => "list_notes".to_owned(),
        kernel::Command::ListMembers => "list_members".to_owned(),
    }
}

fn note(word: &str) -> kernel::Note {
    match word.split(':').collect::<Vec<_>>().as_slice() {
        [id, owner, shared, body] => kernel::Note {
            id: number(id),
            owner: number(owner),
            shared: flag(shared),
            body: text(body),
        },
        _ => panic!("bad note {word}"),
    }
}

fn member(word: &str) -> kernel::Member {
    match word.split(':').collect::<Vec<_>>().as_slice() {
        [user, admin] => kernel::Member {
            user: number(user),
            admin: flag(admin),
        },
        _ => panic!("bad member {word}"),
    }
}

fn reply(words: &[&str]) -> kernel::Reply {
    match words {
        ["done"] => kernel::Reply::Done,
        ["found", n] => kernel::Reply::Found { n: note(n) },
        ["notes", ns @ ..] => kernel::Reply::Notes {
            ns: ns.iter().map(|n| note(n)).collect(),
        },
        ["members", ms @ ..] => kernel::Reply::Members {
            ms: ms.iter().map(|m| member(m)).collect(),
        },
        _ => panic!("bad reply {words:?}"),
    }
}

fn show_note(n: &kernel::Note) -> String {
    format!(
        "{}:{}:{}:{}",
        n.id,
        n.owner,
        show_flag(n.shared),
        show(n.body.as_bytes())
    )
}

fn show_reply(reply: &kernel::Reply) -> String {
    let words: Vec<String> = match reply {
        kernel::Reply::Done => vec!["done".to_owned()],
        kernel::Reply::Found { n } => vec!["found".to_owned(), show_note(n)],
        kernel::Reply::Notes { ns } => std::iter::once("notes".to_owned())
            .chain(ns.iter().map(show_note))
            .collect(),
        kernel::Reply::Members { ms } => std::iter::once("members".to_owned())
            .chain(
                ms.iter()
                    .map(|m| format!("{}:{}", m.user, show_flag(m.admin))),
            )
            .collect(),
    };
    words.join(" ")
}

/// The JSON value of a reply. serde_json writes the members of an object in the order of their
/// keys.
fn reply_value(reply: &kernel::Reply) -> Value {
    let note = |n: &kernel::Note| json!({ "id": n.id, "owner": n.owner, "shared": n.shared, "body": n.body });
    let member = |m: &kernel::Member| json!({ "user": m.user, "admin": m.admin });
    match reply {
        kernel::Reply::Done => json!({ "done": true }),
        kernel::Reply::Found { n } => json!({ "note": note(n) }),
        kernel::Reply::Notes { ns } => json!({ "notes": ns.iter().map(note).collect::<Vec<_>>() }),
        kernel::Reply::Members { ms } => {
            json!({ "members": ms.iter().map(member).collect::<Vec<_>>() })
        }
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

#[derive(Default)]
struct Counts {
    accepted: usize,
    replies: usize,
    stored: usize,
}

fn run(line: &str, counts: &mut Counts) -> String {
    let words: Vec<&str> = line.split(' ').collect();
    match words.as_slice() {
        ["request", tenant, user, exp, now, b] => {
            match wire::request(
                number(tenant),
                number(user),
                number(exp),
                number(now),
                body(b),
            ) {
                Ok(call) => {
                    counts.accepted += 1;
                    format!(
                        "ok {} {} {}",
                        call.actor.org,
                        call.actor.user,
                        show_command(&call.cmd)
                    )
                }
                Err(r) => show_response("err", &r),
            }
        }
        ["respond", "ok", r @ ..] => {
            let reply = reply(r);
            let answer = wire::respond(Ok(reply.clone()));
            assert_eq!(answer.body, wire::encode_reply(reply.clone()), "{line}");
            assert_eq!(
                answer.body,
                serde_json::to_vec(&reply_value(&reply)).expect("JSON"),
                "serde_json on {line}"
            );
            let stored = String::from_utf8(answer.body.clone()).expect("a reply is UTF-8");
            assert_eq!(wire::decode_reply(stored), Some(reply), "read back: {line}");
            counts.replies += 1;
            show_response("resp", &answer)
        }
        ["respond", "err", name] => {
            let refusal = match *name {
                "denied" => Refusal::Denied,
                "not_found" => Refusal::App {
                    e: kernel::Error::NotFound,
                },
                "bad_text" => Refusal::App {
                    e: kernel::Error::BadText,
                },
                _ => panic!("bad refusal {name}"),
            };
            show_response("resp", &wire::respond(Err(refusal)))
        }
        ["fingerprint", cmd @ ..] => {
            let cmd = command(cmd);
            let bytes = wire::fingerprint(cmd.clone());
            if !matches!(cmd, kernel::Command::PutNote { .. }) {
                assert_eq!(bytes, format!("{cmd:?}").into_bytes(), "the stored form");
            }
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
        ["stored", b] => match wire::decode_reply(text(b)) {
            Some(reply) => {
                counts.stored += 1;
                format!("reply {}", show_reply(&reply))
            }
            None => "none".to_owned(),
        },
        _ => panic!("bad line {line}"),
    }
}

fn oracle() -> String {
    let path = std::env::var("LEANGAGE_NOTES_REQUEST_ORACLE")
        .expect("LEANGAGE_NOTES_REQUEST_ORACLE is required");
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
fn generated_rust_notes_wire_functions_agree_with_lean() {
    let mut counts = Counts::default();
    let ours: Vec<String> = CASES.lines().map(|line| run(line, &mut counts)).collect();
    let theirs = oracle();
    assert_eq!(ours.len(), theirs.lines().count());
    assert!(counts.accepted > 500, "{} bodies accepted", counts.accepted);
    assert!(counts.replies > 300, "{} replies written", counts.replies);
    assert!(counts.stored > 100, "{} stored replies read", counts.stored);
    for (i, (a, b)) in ours.iter().zip(theirs.lines()).enumerate() {
        assert_eq!(a, b, "line {}: {}", i + 1, CASES.lines().nth(i).unwrap());
    }
}
