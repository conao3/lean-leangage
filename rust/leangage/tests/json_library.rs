//! What serde_json does, through `json_text::tokens` and the generated `json_lexemes::number_of`,
//! with the texts on which the JSON libraries of the three servers differ or might: `None` for a
//! text it refuses, and the tokens of a text it reads.

use leangage::json_lexemes::{self, Lexeme};
use leangage::json_text;

/// A token, with a number as `number_of` reads it and a string and a key as their bytes.
#[derive(Clone, Debug, PartialEq)]
enum Item {
    Null,
    Bool { b: bool },
    Num { n: u64 },
    Number,
    Str { s: Vec<u8> },
    Key { s: Vec<u8> },
    ArrOpen,
    ArrClose,
    ObjOpen,
    ObjClose,
}

fn item(lexeme: Lexeme) -> Item {
    match lexeme {
        Lexeme::Null => Item::Null,
        Lexeme::Bool { b } => Item::Bool { b },
        Lexeme::Number { text } => match json_lexemes::number_of(text) {
            Some(n) => Item::Num { n },
            None => Item::Number,
        },
        Lexeme::Str { s } => Item::Str { s: s.into_bytes() },
        Lexeme::Key { s } => Item::Key { s: s.into_bytes() },
        Lexeme::ArrOpen => Item::ArrOpen,
        Lexeme::ArrClose => Item::ArrClose,
        Lexeme::ObjOpen => Item::ObjOpen,
        Lexeme::ObjClose => Item::ObjClose,
    }
}

/// The name of a text, its bytes and what serde_json makes of them.
type Case = (&'static str, Vec<u8>, Option<Vec<Item>>);

fn read(bytes: &[u8]) -> Option<Vec<Item>> {
    json_text::tokens(bytes).map(|tokens| {
        json_lexemes::tokens_lexemes(tokens)
            .into_iter()
            .map(item)
            .collect()
    })
}

fn nested(depth: usize) -> Vec<u8> {
    let mut text = vec![b'['; depth];
    text.extend(vec![b']'; depth]);
    text
}

fn key(s: &str) -> Item {
    Item::Key {
        s: s.as_bytes().to_vec(),
    }
}

fn string(s: &str) -> Item {
    Item::Str {
        s: s.as_bytes().to_vec(),
    }
}

#[test]
fn serde_json_reads_and_refuses() {
    let num = |n| Item::Num { n };
    let cases: Vec<Case> = vec![
        ("lone high surrogate", br#""\ud800""#.to_vec(), None),
        ("lone low surrogate", br#""\udc00""#.to_vec(), None),
        (
            "surrogate pair",
            br#""\ud83d\ude00""#.to_vec(),
            Some(vec![string("\u{1f600}")]),
        ),
        (
            "depth 127",
            nested(127),
            Some([vec![Item::ArrOpen; 127], vec![Item::ArrClose; 127]].concat()),
        ),
        ("depth 128", nested(128), None),
        ("depth 200", nested(200), None),
        ("depth 2000", nested(2000), None),
        ("NaN", b"NaN".to_vec(), None),
        ("Infinity", b"Infinity".to_vec(), None),
        ("-Infinity", b"-Infinity".to_vec(), None),
        ("1e400", b"1e400".to_vec(), None),
        ("-0", b"-0".to_vec(), Some(vec![Item::Number])),
        ("1.0", b"1.0".to_vec(), Some(vec![Item::Number])),
        ("1e2", b"1e2".to_vec(), Some(vec![Item::Number])),
        ("-5", b"-5".to_vec(), Some(vec![Item::Number])),
        (
            "2^64 - 1",
            b"18446744073709551615".to_vec(),
            Some(vec![num(u64::MAX)]),
        ),
        (
            "2^64",
            b"18446744073709551616".to_vec(),
            Some(vec![Item::Number]),
        ),
        ("leading zero", b"01".to_vec(), None),
        ("two objects", b"{} {}".to_vec(), None),
        ("two numbers", b"1 2".to_vec(), None),
        ("one bracket more", b"[]]".to_vec(), None),
        (
            "a member twice",
            br#"{"a":1,"a":2}"#.to_vec(),
            Some(vec![
                Item::ObjOpen,
                key("a"),
                num(1),
                key("a"),
                num(2),
                Item::ObjClose,
            ]),
        ),
        (
            "upper-case key",
            br#"{"CMD":"get"}"#.to_vec(),
            Some(vec![
                Item::ObjOpen,
                key("CMD"),
                string("get"),
                Item::ObjClose,
            ]),
        ),
        ("byte order mark", b"\xef\xbb\xbf{}".to_vec(), None),
        ("UTF-16", b"{\0}\0".to_vec(), None),
        ("not UTF-8 in a string", b"\"\xff\"".to_vec(), None),
        ("control character in a string", b"\"\x01\"".to_vec(), None),
        ("empty", b"".to_vec(), None),
        ("spaces only", b" \n".to_vec(), None),
        (
            "spaces around",
            b" {\t\"a\" :\n1 }\r\n".to_vec(),
            Some(vec![Item::ObjOpen, key("a"), num(1), Item::ObjClose]),
        ),
    ];
    for (name, bytes, expected) in cases {
        assert_eq!(read(&bytes), expected, "{name}");
    }
}
