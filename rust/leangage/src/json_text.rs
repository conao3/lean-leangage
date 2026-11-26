//! The tokens of a JSON text, read with serde_json: the one file of the server that calls a JSON
//! library. `lexemes` hands the tokens over in the order of the document, a member twice as two
//! members, and decides nothing about them; the generated functions of `json_lexemes` and of the
//! kernels do. A number serde_json reads as a `u64` is handed over as its decimal digits, and
//! every other number as a text with a sign or an exponent.

use std::fmt;

use serde::de::{DeserializeSeed, Deserializer, Error, MapAccess, SeqAccess, Visitor};

use crate::json_lexemes::Lexeme;

/// A value, whose tokens go to the end of the list.
struct Value<'a>(&'a mut Vec<Lexeme>);

/// The name of a member.
struct Key<'a>(&'a mut Vec<Lexeme>);

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
        self.0.push(Lexeme::Null);
        Ok(())
    }

    fn visit_bool<E: Error>(self, b: bool) -> Result<(), E> {
        self.0.push(Lexeme::Bool { b });
        Ok(())
    }

    fn visit_u64<E: Error>(self, n: u64) -> Result<(), E> {
        self.0.push(Lexeme::Number {
            text: n.to_string(),
        });
        Ok(())
    }

    fn visit_i64<E: Error>(self, n: i64) -> Result<(), E> {
        self.0.push(Lexeme::Number {
            text: format!("{n:+}"),
        });
        Ok(())
    }

    fn visit_f64<E: Error>(self, x: f64) -> Result<(), E> {
        self.0.push(Lexeme::Number {
            text: format!("{x:e}"),
        });
        Ok(())
    }

    fn visit_str<E: Error>(self, s: &str) -> Result<(), E> {
        self.0.push(Lexeme::Str { s: s.to_owned() });
        Ok(())
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<(), A::Error> {
        self.0.push(Lexeme::ArrOpen);
        while seq.next_element_seed(Value(self.0))?.is_some() {}
        self.0.push(Lexeme::ArrClose);
        Ok(())
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        self.0.push(Lexeme::ObjOpen);
        while map.next_key_seed(Key(self.0))?.is_some() {
            map.next_value_seed(Value(self.0))?;
        }
        self.0.push(Lexeme::ObjClose);
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
        self.0.push(Lexeme::Key { s: s.to_owned() });
        Ok(())
    }
}

/// The tokens of the JSON text the bytes are, or `None` for bytes serde_json refuses.
pub fn lexemes(bytes: &[u8]) -> Option<Vec<Lexeme>> {
    let mut out = Vec::with_capacity(16);
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    Value(&mut out).deserialize(&mut deserializer).ok()?;
    deserializer.end().ok()?;
    Some(out)
}
