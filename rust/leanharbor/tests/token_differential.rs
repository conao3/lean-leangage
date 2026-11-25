//! The generated Rust token functions against the ones run natively by Lean (`token-oracle`), on
//! the shared token list. The line format is described in `lean/TokenOracle.lean`.

use std::io::Write as _;
use std::process::{Command, Stdio};

use leanharbor::token_format;

const CASES: &str = include_str!("../../../testdata/token-cases.txt");

fn bytes(s: &str) -> Vec<u8> {
    let hex = s.strip_prefix('x').expect("bytes start with x");
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect()
}

fn show(bytes: &[u8]) -> String {
    let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("x{hex}")
}

fn run(line: &str) -> String {
    let words: Vec<&str> = line.split(' ').collect();
    let number = |s: &str| s.parse::<u64>().expect("a u64");
    match words.as_slice() {
        ["parse", tok] => match token_format::parse(bytes(tok)) {
            None => "none".to_string(),
            Some(p) => format!(
                "parsed {} {} {} {} {}",
                p.tenant,
                p.user,
                p.exp,
                show(&p.payload),
                show(&p.sig)
            ),
        },
        ["issue", t, u, e, sig] => {
            let payload = token_format::encode_payload(number(t), number(u), number(e));
            format!("token {}", show(&token_format::join(payload, bytes(sig))))
        }
        _ => panic!("bad line {line}"),
    }
}

fn oracle() -> String {
    let path =
        std::env::var("LEANHARBOR_TOKEN_ORACLE").expect("LEANHARBOR_TOKEN_ORACLE is required");
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
fn generated_rust_token_functions_agree_with_lean() {
    let ours: Vec<String> = CASES.lines().map(run).collect();
    let theirs = oracle();
    assert_eq!(ours.len(), theirs.lines().count());
    assert!(ours.iter().filter(|l| l.starts_with("parsed ")).count() > 100);
    assert!(ours.iter().filter(|l| *l == "none").count() > 100);
    for (i, (a, b)) in ours.iter().zip(theirs.lines()).enumerate() {
        assert_eq!(a, b, "line {}: {}", i + 1, CASES.lines().nth(i).unwrap());
    }
}
