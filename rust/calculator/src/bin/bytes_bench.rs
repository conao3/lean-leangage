//! Times the byte functions the shells call on every request: (a) the check of one token (split
//! and HMAC), (b) the bytes of one calculator reply and (c) the bytes of a notes list of 20 notes
//! with bodies of 200 bytes.

use std::hint::black_box;
use std::time::Instant;

use hmac::{Hmac, Mac};
use leanharbor::http::Api;
use leanharbor::json_format::{self, Tok};
use leanharbor::token::{self, Claims};
use leanharbor::token_format;
use leanharbor_calculator::{Calculator, kernel};
use leanharbor_notes::{Notes, kernel as notes};
use sha2::Sha256;

const ROUNDS: usize = 5;

fn time(label: &str, iterations: u32, mut f: impl FnMut()) {
    let mut rounds: Vec<f64> = (0..ROUNDS)
        .map(|_| {
            let start = Instant::now();
            for _ in 0..iterations {
                f();
            }
            start.elapsed().as_nanos() as f64 / f64::from(iterations)
        })
        .collect();
    rounds.sort_by(f64::total_cmp);
    println!(
        "{label:<28} median {:>10.0} ns  min {:>10.0} ns",
        rounds[ROUNDS / 2],
        rounds[0]
    );
}

/// The tokens `Notes::encode_reply` writes for a list of notes.
fn notes_toks(reply: &notes::Reply) -> Vec<Tok> {
    let notes::Reply::Notes { ns } = reply else {
        unreachable!("a list of notes")
    };
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

fn main() {
    let secret = b"bench-secret".to_vec();
    let claims = Claims {
        tenant: 1,
        user: 42,
        expiry: 4_102_444_800,
    };
    let tok = token::issue(&secret, claims);
    time("(a) token verify", 200_000, || {
        black_box(token::verify(black_box(&secret), black_box(&tok), 0)).expect("a valid token");
    });
    time("    split only", 200_000, || {
        black_box(token_format::parse(black_box(&tok).as_bytes().to_vec()));
    });
    let payload = &tok.as_bytes()[..tok.rfind('.').expect("a token has dots")];
    time("    HMAC only", 200_000, || {
        let mut mac = Hmac::<Sha256>::new_from_slice(black_box(&secret)).expect("any key length");
        mac.update(black_box(payload));
        black_box(mac.finalize());
    });

    let reply = kernel::Reply { v: 6 };
    time("(b) calculator reply", 200_000, || {
        black_box(<Calculator as Api<Calculator>>::encode_reply(black_box(
            &reply,
        )));
    });

    let list = notes::Reply::Notes {
        ns: (0..20)
            .map(|i| notes::Note {
                id: i,
                owner: 7,
                shared: i % 2 == 0,
                body: "n".repeat(200),
            })
            .collect(),
    };
    assert_eq!(
        json_format::write(notes_toks(&list)),
        <Notes as Api<Notes>>::encode_reply(&list)
    );
    time("(c) notes list of 20", 2_000, || {
        black_box(<Notes as Api<Notes>>::encode_reply(black_box(&list)));
    });
    let toks = notes_toks(&list);
    time("    write only", 2_000, || {
        black_box(json_format::write(black_box(&toks).clone()));
    });
}
