//! The generated Rust JSON writer against the one run natively by Lean (`json-oracle`), on the
//! shared token lists. The line format is described in `lean/JsonOracle.lean`. A list whose
//! strings are UTF-8 is also written by `write_array`, which must write what `write` writes.

use std::io::Write as _;
use std::process::{Command, Stdio};

use leanharbor::json_format::{self, StrTok, Tok};

const CASES: &str = include_str!("../../../testdata/json-cases.txt");

fn bytes(hex: &str) -> Vec<u8> {
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect()
}

fn show(bytes: &[u8]) -> String {
    let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("x{hex}")
}

fn tok(word: &str) -> Tok {
    match word {
        "n" => Tok::Null,
        "t" => Tok::Bool { b: true },
        "f" => Tok::Bool { b: false },
        "[" => Tok::ArrOpen,
        "]" => Tok::ArrClose,
        "{" => Tok::ObjOpen,
        "}" => Tok::ObjClose,
        _ => {
            if let Some(n) = word.strip_prefix('u') {
                Tok::Num {
                    n: n.parse().expect("a u64"),
                }
            } else if let Some(s) = word.strip_prefix("sx") {
                Tok::Str { s: bytes(s) }
            } else if let Some(s) = word.strip_prefix("kx") {
                Tok::Key { s: bytes(s) }
            } else {
                panic!("bad token {word}")
            }
        }
    }
}

fn str_tok(t: &Tok) -> Option<StrTok> {
    let text = |s: &[u8]| String::from_utf8(s.to_vec()).ok();
    Some(match t {
        Tok::Null => StrTok::Null,
        Tok::Bool { b } => StrTok::Bool { b: *b },
        Tok::Num { n } => StrTok::Num { n: *n },
        Tok::Str { s } => StrTok::Str { s: text(s)? },
        Tok::Key { s } => StrTok::Key { s: text(s)? },
        Tok::ArrOpen => StrTok::ArrOpen,
        Tok::ArrClose => StrTok::ArrClose,
        Tok::ObjOpen => StrTok::ObjOpen,
        Tok::ObjClose => StrTok::ObjClose,
    })
}

fn run(line: &str) -> String {
    let mut words = line.split(' ');
    assert_eq!(words.next(), Some("write"), "bad line {line}");
    let toks: Vec<Tok> = words.map(tok).collect();
    let written = json_format::write(toks.clone());
    if let Some(str_toks) = toks.iter().map(str_tok).collect::<Option<Vec<_>>>() {
        assert_eq!(
            json_format::write_array(str_toks),
            written,
            "write_array of {line}"
        );
    }
    format!("json {}", show(&written))
}

fn oracle() -> String {
    let path = std::env::var("LEANHARBOR_JSON_ORACLE").expect("LEANHARBOR_JSON_ORACLE is required");
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
fn generated_rust_json_writer_agrees_with_lean() {
    let ours: Vec<String> = CASES.lines().map(run).collect();
    let theirs = oracle();
    assert_eq!(ours.len(), theirs.lines().count());
    let utf8 = CASES
        .lines()
        .filter(|l| l.split(' ').skip(1).map(tok).all(|t| str_tok(&t).is_some()))
        .count();
    assert!(utf8 > 1000);
    for (i, (a, b)) in ours.iter().zip(theirs.lines()).enumerate() {
        assert_eq!(a, b, "line {}: {}", i + 1, CASES.lines().nth(i).unwrap());
    }
}
