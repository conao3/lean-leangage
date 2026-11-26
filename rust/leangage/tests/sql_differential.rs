//! The generated Rust SQL compiler against the one run natively by Lean (`sql-oracle`), on the
//! shared statement list. The line format is described in `lean/SqlOracle.lean`.

use std::io::Write as _;
use std::process::{Command, Stdio};

use leanfran::runtime::Nat;
use leangage::sql::{self, Col, Kind, Tab, Val, Write};

const STATEMENTS: &str = include_str!("../../../testdata/sql-statements.txt");

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex"))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn text(s: &str) -> String {
    String::from_utf8(unhex(s)).expect("utf-8")
}

fn nat(s: &str) -> Nat {
    Nat::from(s.parse::<u64>().expect("a number"))
}

fn value(s: &str) -> Val {
    match s.split_at(1) {
        ("i", v) => Val::Int {
            v: v.parse().expect("an int64"),
        },
        ("b", "0") => Val::Bool { v: false },
        ("b", "1") => Val::Bool { v: true },
        ("t", v) => Val::Text { v: text(v) },
        ("y", v) => Val::Bytes { v: unhex(v) },
        ("n", "") => Val::Null,
        _ => panic!("bad value {s}"),
    }
}

fn show_value(v: &Val) -> String {
    match v {
        Val::Int { v } => format!("i{v}"),
        Val::Bool { v } => format!("b{}", u8::from(*v)),
        Val::Text { v } => format!("t{}", hex(v.as_bytes())),
        Val::Bytes { v } => format!("y{}", hex(v)),
        Val::Null => "n".to_string(),
    }
}

fn column(s: &str) -> Col {
    let parts: Vec<&str> = s.split(':').collect();
    let kind = match parts[1] {
        "int" => Kind::Int,
        "bool" => Kind::Bool,
        "text" => Kind::Text,
        "bytes" => Kind::Bytes,
        other => panic!("bad kind {other}"),
    };
    Col {
        name: text(parts[0]),
        kind,
        nullable: parts[2] == "1",
    }
}

fn show(compiled: Option<(sql::Sql, Vec<Val>)>) -> String {
    match compiled {
        None => "none".to_string(),
        Some((q, ps)) => {
            let mut words = vec!["sql".to_string(), hex(sql::render(q).as_bytes())];
            words.extend(ps.iter().map(show_value));
            words.join(" ")
        }
    }
}

fn run(schema: &mut Vec<Tab>, line: &str) -> String {
    let words: Vec<&str> = line.split(' ').collect();
    let tenant = |s: &str| s.parse::<i64>().expect("an int64");
    let values = |ws: &[&str]| ws.iter().map(|w| value(w)).collect::<Vec<_>>();
    let compile =
        |schema: &Vec<Tab>, tv: i64, w: Write| show(sql::compile(schema.clone(), tv, sql::plan(w)));
    match words.as_slice() {
        ["reset"] => {
            schema.clear();
            "ok".to_string()
        }
        ["table", name, kl, cols @ ..] => {
            schema.push(Tab {
                name: text(name),
                cols: cols.iter().map(|c| column(c)).collect(),
                kl: nat(kl),
            });
            format!("valid {}", sql::valid(schema.clone()))
        }
        ["create"] => {
            let mut words = vec!["create".to_string()];
            words.extend(
                schema
                    .iter()
                    .map(|t| hex(sql::render(sql::create(t.clone())).as_bytes())),
            );
            words.join(" ")
        }
        ["put", tv, t, kl, vs @ ..] => compile(
            schema,
            tenant(tv),
            Write::Put {
                table: nat(t),
                key_len: nat(kl),
                row: values(vs),
            },
        ),
        ["del", tv, t, vs @ ..] => compile(
            schema,
            tenant(tv),
            Write::Del {
                table: nat(t),
                key: values(vs),
            },
        ),
        ["delwhere", tv, t, i, v] => compile(
            schema,
            tenant(tv),
            Write::DelWhere {
                table: nat(t),
                col: nat(i),
                val: value(v),
            },
        ),
        ["select", tv, t] => show(sql::select(schema.clone(), tenant(tv), nat(t), None)),
        ["select", tv, t, i, v] => show(sql::select(
            schema.clone(),
            tenant(tv),
            nat(t),
            Some((nat(i), value(v))),
        )),
        _ => panic!("bad line {line}"),
    }
}

fn oracle() -> String {
    let path = std::env::var("LEANGAGE_SQL_ORACLE").expect("LEANGAGE_SQL_ORACLE is required");
    let mut child = Command::new(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("the oracle starts");
    let mut stdin = child.stdin.take().expect("stdin is piped");
    let writer = std::thread::spawn(move || stdin.write_all(STATEMENTS.as_bytes()));
    let output = child.wait_with_output().expect("the oracle runs");
    writer
        .join()
        .expect("writer")
        .expect("statements are written");
    assert!(output.status.success());
    String::from_utf8(output.stdout).expect("utf-8")
}

#[test]
fn generated_rust_sql_agrees_with_lean() {
    let mut schema = Vec::new();
    let ours: Vec<String> = STATEMENTS
        .lines()
        .map(|line| run(&mut schema, line))
        .collect();
    let theirs = oracle();
    assert_eq!(ours.len(), theirs.lines().count());
    assert!(ours.iter().filter(|l| l.starts_with("sql ")).count() > 100);
    for (i, (a, b)) in ours.iter().zip(theirs.lines()).enumerate() {
        assert_eq!(
            a,
            b,
            "line {}: {}",
            i + 1,
            STATEMENTS.lines().nth(i).unwrap()
        );
    }
}
