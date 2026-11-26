//! Times the byte functions the servers call on every request: (a) the check of one token (split
//! and HMAC), (b) the bytes of one calculator reply and (c) the bytes of a notes list of 20 notes
//! with bodies of 200 bytes. Each line times the functions over lists (`parse`, `encode_reply`,
//! `write`) and the functions the servers call (`parse_string`, `encode_reply_array`,
//! `write_array`) in alternating rounds.

use std::hint::black_box;
use std::time::Instant;

use hmac::{Hmac, Mac};
use leangage::http::Api;
use leangage::json_format::{self, StrTok, Tok};
use leangage::token::{self, Claims};
use leangage::token_format;
use leangage_calculator::{Calculator, kernel};
use leangage_notes::{Notes, kernel as notes};
use sha2::Sha256;

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

/// Prints the minimum and the median of the rounds, lists first.
fn compare(label: &str, iterations: u32, mut lists: impl FnMut(), mut arrays: impl FnMut()) {
    let mut old = Vec::new();
    let mut new = Vec::new();
    for _ in 0..ROUNDS {
        old.push(per_op(iterations, &mut lists));
        new.push(per_op(iterations, &mut arrays));
    }
    println!(
        "{label:<22} lists {}  arrays {}",
        show(&mut old),
        show(&mut new)
    );
}

fn tag(secret: &[u8], payload: &[u8]) -> Hmac<Sha256> {
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).expect("HMAC takes a key of any length");
    mac.update(payload);
    mac
}

/// `token::verify` with `parse` in place of `parse_string`.
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
    assert_eq!(token::verify(&secret, &tok, 0), Ok(claims));
    compare(
        "(a) token check",
        100_000,
        || {
            black_box(verify_lists(black_box(&secret), black_box(&tok), 0));
        },
        || {
            black_box(token::verify(black_box(&secret), black_box(&tok), 0)).ok();
        },
    );
    compare(
        "    split only",
        100_000,
        || {
            black_box(token_format::parse(black_box(&tok).as_bytes().to_vec()));
        },
        || {
            black_box(token_format::parse_string(black_box(&tok)));
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
        <Calculator as Api<Calculator>>::encode_reply(&reply)
    );
    compare(
        "(b) calculator reply",
        100_000,
        || {
            black_box(kernel::encode_reply(black_box(&reply).clone()));
        },
        || {
            black_box(<Calculator as Api<Calculator>>::encode_reply(black_box(
                &reply,
            )));
        },
    );

    let ns = note_list();
    let list = notes::Reply::Notes { ns: ns.clone() };
    let body = <Notes as Api<Notes>>::encode_reply(&list);
    assert_eq!(json_format::write(notes_toks(&ns)), body);
    assert_eq!(json_format::write_array(notes_str_toks(&ns)), body);
    compare(
        "(c) notes list of 20",
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
            black_box(<Notes as Api<Notes>>::encode_reply(black_box(&list)));
        }));
    }
    println!("    Notes::encode_reply {}", show(&mut server));
}
