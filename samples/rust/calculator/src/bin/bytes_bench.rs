//! Times the byte functions the servers call on every request: (a) the check of one token (split
//! and HMAC), (b) the bytes of one calculator reply and (c) the bytes of a notes list of 20 notes
//! with bodies of 200 bytes. Each line times the functions over lists (`parse`, `encode_reply`,
//! `write`) and the functions over strings and arrays (`authenticate`, `encode_reply_array`,
//! `write_array`) in alternating rounds. (d) times the reading of one request body into a
//! command, written without a space and as Python's `json.dumps` writes it, and (e) the answer
//! to an accepted command, each written by hand with serde_json and as the calculator server
//! does it: `body_of`, which reads the body with serde_json into tokens, with the generated
//! `wire::request`, and the generated `wire::respond`. (d) also times `body_of` alone, a copy of
//! the tokens it gives, `wire::request` on such a copy with a token that is valid and with one
//! that has expired (which answers before it decodes), and prints the calls per second. (f) times
//! what the server does for one request without a socket: the router of `POST /rpc` called in
//! process, which checks the token, reads the body, runs the command on the memory engine and
//! makes the answer.

use std::hint::black_box;
use std::sync::Arc;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use axum::body::Body;
use axum::http::Request;

use hmac::{Hmac, Mac};
use leangage::Storage;
use leangage::http::{body_of, rpc_router};
use leangage::http_format;
use leangage::json_format::{self, StrTok, Tok};
use leangage::memory::MemoryEngine;
use leangage::token::{self, Claims};
use leangage::token_format;
use leangage_calculator::{Calculator, kernel, wire};
use leangage_notes::{Notes, kernel as notes};
use serde::Deserialize;
use sha2::Sha256;
use tower::ServiceExt;

const ROUNDS: usize = 7;

fn per_op(iterations: u32, f: &mut impl FnMut()) -> f64 {
    let start = Instant::now();
    for _ in 0..iterations {
        f();
    }
    start.elapsed().as_nanos() as f64 / f64::from(iterations)
}

fn show(rounds: &mut [f64]) -> String {
    rounds.sort_by(f64::total_cmp);
    format!("{:>9.0} ns (median {:>9.0})", rounds[0], rounds[ROUNDS / 2])
}

/// Prints the minimum and the median of the rounds of the two, named `names`, and returns the
/// medians.
fn compare(
    label: &str,
    names: (&str, &str),
    iterations: u32,
    mut lists: impl FnMut(),
    mut arrays: impl FnMut(),
) -> (f64, f64) {
    let mut old = Vec::new();
    let mut new = Vec::new();
    for _ in 0..ROUNDS {
        old.push(per_op(iterations, &mut lists));
        new.push(per_op(iterations, &mut arrays));
    }
    println!(
        "{label:<22} {} {}  {} {}",
        names.0,
        show(&mut old),
        names.1,
        show(&mut new)
    );
    (old[ROUNDS / 2], new[ROUNDS / 2])
}

fn tag(secret: &[u8], payload: &[u8]) -> Hmac<Sha256> {
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).expect("HMAC takes a key of any length");
    mac.update(payload);
    mac
}

/// The check of a token with `parse`, the tag and the expiry, written by hand.
fn verify_lists(secret: &[u8], tok: &str, now: u64) -> Option<Claims> {
    let parsed = token_format::parse(tok.as_bytes().to_vec())?;
    tag(secret, &parsed.payload)
        .verify_slice(&parsed.sig)
        .ok()?;
    (parsed.exp >= now).then_some(Claims {
        tenant: parsed.tenant,
        user: parsed.user,
        expiry: parsed.exp,
    })
}

#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum WireOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Deserialize)]
#[serde(tag = "cmd", rename_all = "snake_case", deny_unknown_fields)]
enum WireCommand {
    Set { value: u64 },
    Apply { op: WireOp, arg: u64 },
    Get,
}

/// A body read into a command with serde_json, written by hand.
fn decode_by_hand(body: &[u8]) -> Option<kernel::Command> {
    let value: serde_json::Value = serde_json::from_slice(body).ok()?;
    Some(match serde_json::from_value(value).ok()? {
        WireCommand::Set { value } => kernel::Command::Set { value },
        WireCommand::Apply { op, arg } => kernel::Command::Apply {
            op: match op {
                WireOp::Add => kernel::Op::Add,
                WireOp::Sub => kernel::Op::Sub,
                WireOp::Mul => kernel::Op::Mul,
                WireOp::Div => kernel::Op::Div,
            },
            arg,
        },
        WireCommand::Get => kernel::Command::Get,
    })
}

fn note_list() -> Vec<notes::Note> {
    (0..20)
        .map(|i| notes::Note {
            id: i,
            owner: 7,
            shared: i % 2 == 0,
            body: "n".repeat(200),
        })
        .collect()
}

/// The tokens `Notes::encode_reply` writes for a list of notes, over lists.
fn notes_toks(ns: &[notes::Note]) -> Vec<Tok> {
    let mut out = vec![
        Tok::ObjOpen,
        Tok::Key {
            s: b"notes".to_vec(),
        },
        Tok::ArrOpen,
    ];
    for n in ns {
        out.extend([
            Tok::ObjOpen,
            Tok::Key {
                s: b"body".to_vec(),
            },
            Tok::Str {
                s: n.body.as_bytes().to_vec(),
            },
            Tok::Key { s: b"id".to_vec() },
            Tok::Num { n: n.id },
            Tok::Key {
                s: b"owner".to_vec(),
            },
            Tok::Num { n: n.owner },
            Tok::Key {
                s: b"shared".to_vec(),
            },
            Tok::Bool { b: n.shared },
            Tok::ObjClose,
        ]);
    }
    out.extend([Tok::ArrClose, Tok::ObjClose]);
    out
}

/// The same tokens, with strings.
fn notes_str_toks(ns: &[notes::Note]) -> Vec<StrTok> {
    let key = |s: &str| StrTok::Key { s: s.to_owned() };
    let mut out = vec![StrTok::ObjOpen, key("notes"), StrTok::ArrOpen];
    for n in ns {
        out.extend([
            StrTok::ObjOpen,
            key("body"),
            StrTok::Str { s: n.body.clone() },
            key("id"),
            StrTok::Num { n: n.id },
            key("owner"),
            StrTok::Num { n: n.owner },
            key("shared"),
            StrTok::Bool { b: n.shared },
            StrTok::ObjClose,
        ]);
    }
    out.extend([StrTok::ArrClose, StrTok::ObjClose]);
    out
}

fn main() {
    let secret = b"bench-secret".to_vec();
    let claims = Claims {
        tenant: 1,
        user: 42,
        expiry: 4_102_444_800,
    };
    let tok = token::issue(&secret, claims);
    assert_eq!(verify_lists(&secret, &tok, 0), Some(claims));
    let header = format!("Bearer {tok}");
    assert_eq!(token::admit(&secret, Some(&header)).ok(), Some(claims));
    compare(
        "(a) token check",
        ("lists", "arrays"),
        100_000,
        || {
            black_box(verify_lists(black_box(&secret), black_box(&tok), 0));
        },
        || {
            black_box(token::admit(black_box(&secret), Some(black_box(&header)))).ok();
        },
    );
    compare(
        "    split only",
        ("lists", "arrays"),
        100_000,
        || {
            black_box(token_format::parse(black_box(&tok).as_bytes().to_vec()));
        },
        || {
            black_box(http_format::authenticate(Some(black_box(&header).clone()))).ok();
        },
    );
    let payload = &tok.as_bytes()[..tok.rfind('.').expect("a token has dots")];
    let mut hmac = Vec::new();
    for _ in 0..ROUNDS {
        hmac.push(per_op(100_000, &mut || {
            black_box(tag(black_box(&secret), black_box(payload)).finalize());
        }));
    }
    println!("    HMAC only          {}", show(&mut hmac));

    let reply = kernel::Reply { v: 6 };
    assert_eq!(
        kernel::encode_reply(reply.clone()),
        kernel::encode_reply_array(reply.clone())
    );
    compare(
        "(b) calculator reply",
        ("lists", "arrays"),
        100_000,
        || {
            black_box(kernel::encode_reply(black_box(&reply).clone()));
        },
        || {
            black_box(kernel::encode_reply_array(black_box(&reply).clone()));
        },
    );

    let ns = note_list();
    let list = notes::Reply::Notes { ns: ns.clone() };
    let body = <Notes as Storage>::encode_reply(&list);
    assert_eq!(json_format::write(notes_toks(&ns)), body);
    assert_eq!(json_format::write_array(notes_str_toks(&ns)), body);
    compare(
        "(c) notes list of 20",
        ("lists", "arrays"),
        2_000,
        || {
            black_box(json_format::write(notes_toks(black_box(&ns))));
        },
        || {
            black_box(json_format::write_array(notes_str_toks(black_box(&ns))));
        },
    );
    let mut server = Vec::new();
    for _ in 0..ROUNDS {
        server.push(per_op(2_000, &mut || {
            black_box(<Notes as Storage>::encode_reply(black_box(&list)));
        }));
    }
    println!("    Notes::encode_reply {}", show(&mut server));

    let command = kernel::Command::Apply {
        op: kernel::Op::Add,
        arg: 1,
    };
    for (label, body) in [
        ("(d) request body", r#"{"cmd":"apply","op":"add","arg":1}"#),
        (
            "(d) body with spaces",
            r#"{"cmd": "apply", "op": "add", "arg": 1}"#,
        ),
    ] {
        assert_eq!(decode_by_hand(body.as_bytes()), Some(command.clone()));
        assert_eq!(
            wire::request(1, 42, 1, 0, body_of(body.as_bytes()))
                .ok()
                .map(|call| call.cmd),
            Some(command.clone())
        );
        let (by_hand, generated) = compare(
            label,
            ("by hand", "library and generated"),
            100_000,
            || {
                black_box(decode_by_hand(black_box(body).as_bytes()));
            },
            || {
                black_box(wire::request(
                    1,
                    42,
                    1,
                    0,
                    body_of(black_box(body).as_bytes()),
                ))
                .ok();
            },
        );
        let mut library = Vec::new();
        for _ in 0..ROUNDS {
            library.push(per_op(100_000, &mut || {
                black_box(body_of(black_box(body).as_bytes()));
            }));
        }
        println!("    body_of only        {}", show(&mut library));
        let read = body_of(body.as_bytes());
        let (mut copy, mut request, mut expired) = (Vec::new(), Vec::new(), Vec::new());
        for _ in 0..ROUNDS {
            copy.push(per_op(100_000, &mut || {
                black_box(black_box(&read).clone());
            }));
            request.push(per_op(100_000, &mut || {
                black_box(wire::request(1, 42, 1, 0, black_box(&read).clone())).ok();
            }));
            expired.push(per_op(100_000, &mut || {
                black_box(wire::request(1, 42, 0, 1, black_box(&read).clone())).ok();
            }));
        }
        println!("    copy of the tokens  {}", show(&mut copy));
        println!("    request and copy    {}", show(&mut request));
        println!("    expired and copy    {}", show(&mut expired));
        println!(
            "    calls/s: by hand {:.0}, library and generated {:.0}",
            1e9 / by_hand,
            1e9 / generated
        );
    }
    assert_eq!(wire::respond(Ok(reply.clone())).body, br#"{"value":6}"#);
    compare(
        "(e) answer",
        ("by hand", "generated"),
        100_000,
        || {
            black_box((
                200u16,
                kernel::encode_reply_array(black_box(&reply).clone()),
            ));
        },
        || {
            black_box(wire::respond(Ok(black_box(&reply).clone())));
        },
    );

    let secret = b"bench-secret".to_vec();
    let expiry = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
        + 86_400;
    let bearer = format!(
        "Bearer {}",
        token::issue(
            &secret,
            Claims {
                tenant: 1,
                user: 7,
                expiry,
            },
        )
    );
    let router = rpc_router::<Calculator, Calculator, _>(
        Arc::new(MemoryEngine::<Calculator>::new()),
        secret,
    );
    let runtime = tokio::runtime::Builder::new_current_thread()
        .build()
        .expect("a runtime");
    for (label, body) in [
        ("get", r#"{"cmd":"get"}"#),
        ("apply", r#"{"cmd":"apply","op":"div","arg":1}"#),
    ] {
        let call = || {
            let request = Request::post("/rpc")
                .header("authorization", &bearer)
                .header("content-type", "application/json")
                .body(Body::from(body))
                .expect("a request");
            runtime
                .block_on(router.clone().oneshot(request))
                .expect("an answer")
        };
        assert_eq!(call().status(), 200);
        let mut rounds = Vec::new();
        for _ in 0..ROUNDS {
            rounds.push(per_op(50_000, &mut || {
                black_box(call());
            }));
        }
        let line = show(&mut rounds);
        println!(
            "(f) rpc handler, {label:<6} {line}  {:.0} calls/s",
            1e9 / rounds[0]
        );
    }
}
