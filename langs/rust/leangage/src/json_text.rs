//! The tokens of a JSON text, read with serde_json: the one file of the server that calls a JSON
//! library. `tokens` packs the tokens, in the order of the document and a member twice as two
//! members, into one text: one character for the kind of each token, a line feed, and the texts
//! of the numbers, the strings and the keys, each but the last after the count of its characters
//! and a colon. It decides nothing about them; the generated functions of `json_lexemes` and of
//! the kernels do. A number serde_json reads as a `u64` is handed over as its decimal digits, and
//! every other number as a text with a sign or an exponent.

use std::fmt;

use serde::de::{DeserializeSeed, Deserializer, Error, MapAccess, SeqAccess, Visitor};

/// The kinds of the tokens read, their texts with the count of the characters before each, and
/// where the count of the last text starts and ends.
struct Tokens {
    kinds: String,
    texts: String,
    count: usize,
    last: usize,
}

/// `out` followed by the decimal digits of `n`.
fn decimal(out: &mut String, mut n: u64) {
    let mut digits = [0u8; 20];
    let mut start = digits.len();
    loop {
        start -= 1;
        digits[start] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    for digit in &digits[start..] {
        out.push(char::from(*digit));
    }
}

impl Tokens {
    fn text(&mut self, kind: char, text: &str) {
        self.kinds.push(kind);
        self.count = self.texts.len();
        decimal(&mut self.texts, text.chars().count() as u64);
        self.texts.push(':');
        self.last = self.texts.len();
        self.texts.push_str(text);
    }
}

/// A value, whose tokens go to the end of the tokens read.
struct Value<'a>(&'a mut Tokens);

/// The name of a member.
struct Key<'a>(&'a mut Tokens);

impl<'de> DeserializeSeed<'de> for Value<'_> {
    type Value = ();

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<(), D::Error> {
        deserializer.deserialize_any(self)
    }
}

impl<'de> Visitor<'de> for Value<'_> {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("a JSON value")
    }

    fn visit_unit<E: Error>(self) -> Result<(), E> {
        self.0.kinds.push('n');
        Ok(())
    }

    fn visit_bool<E: Error>(self, b: bool) -> Result<(), E> {
        self.0.kinds.push(if b { 't' } else { 'f' });
        Ok(())
    }

    fn visit_u64<E: Error>(self, n: u64) -> Result<(), E> {
        let mut text = String::with_capacity(20);
        decimal(&mut text, n);
        self.0.text('#', &text);
        Ok(())
    }

    fn visit_i64<E: Error>(self, n: i64) -> Result<(), E> {
        self.0.text('#', &format!("{n:+}"));
        Ok(())
    }

    fn visit_f64<E: Error>(self, x: f64) -> Result<(), E> {
        self.0.text('#', &format!("{x:e}"));
        Ok(())
    }

    fn visit_str<E: Error>(self, s: &str) -> Result<(), E> {
        self.0.text('s', s);
        Ok(())
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<(), A::Error> {
        self.0.kinds.push('[');
        while seq.next_element_seed(Value(self.0))?.is_some() {}
        self.0.kinds.push(']');
        Ok(())
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        self.0.kinds.push('{');
        while map.next_key_seed(Key(self.0))?.is_some() {
            map.next_value_seed(Value(self.0))?;
        }
        self.0.kinds.push('}');
        Ok(())
    }
}

impl<'de> DeserializeSeed<'de> for Key<'_> {
    type Value = ();

    fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<(), D::Error> {
        deserializer.deserialize_str(self)
    }
}

impl<'de> Visitor<'de> for Key<'_> {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("the name of a member")
    }

    fn visit_str<E: Error>(self, s: &str) -> Result<(), E> {
        self.0.text('k', s);
        Ok(())
    }
}

/// The packed tokens of the JSON text the bytes are, or `None` for bytes serde_json refuses.
pub fn tokens(bytes: &[u8]) -> Option<String> {
    let mut out = Tokens {
        kinds: String::with_capacity(2 * bytes.len() + 32),
        texts: String::with_capacity(bytes.len() + 32),
        count: 0,
        last: 0,
    };
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    Value(&mut out).deserialize(&mut deserializer).ok()?;
    deserializer.end().ok()?;
    let mut packed = out.kinds;
    packed.push('\n');
    packed.push_str(&out.texts[..out.count]);
    packed.push_str(&out.texts[out.last..]);
    Some(packed)
}
