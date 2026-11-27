//! Bearer tokens: `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`, where the tag
//! signs every byte before the last dot. The bytes are written by functions generated from
//! `langs/lean/Leangage/Token.lean` (`crate::token_format`: `encode_payload` and `join`), and the
//! `Authorization` header is read by `crate::http_format::authenticate`, generated from
//! `langs/lean/Leangage/Http.lean`. This module computes and compares the tag. A [`Verifier`]
//! remembers the headers it accepted, so a header is read and its tag computed once.

use std::collections::HashMap;
use std::sync::RwLock;

use hmac::{Hmac, Mac};
use sha2::Sha256;

use crate::http_format::{self, Failure, Response};
use crate::token_format;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Claims {
    pub tenant: u64,
    pub user: u64,
    pub expiry: u64,
}

fn mac(secret: &[u8], payload: &[u8]) -> Hmac<Sha256> {
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).expect("HMAC takes a key of any length");
    mac.update(payload);
    mac
}

pub fn issue(secret: &[u8], claims: Claims) -> String {
    let payload = token_format::encode_payload(claims.tenant, claims.user, claims.expiry);
    let tag = mac(secret, &payload).finalize().into_bytes().to_vec();
    String::from_utf8(token_format::join(payload, tag)).expect("a token is ASCII")
}

/// The claims of the token in the `Authorization` header when its tag is the HMAC of its
/// payload, or the answer to the request. The expiry is checked by the kernel's `request`.
pub fn admit(secret: &[u8], header: Option<&str>) -> Result<Claims, Response> {
    let bearer = http_format::authenticate(header.map(str::to_owned))?;
    if mac(secret, &bearer.payload)
        .verify_slice(&bearer.sig)
        .is_err()
    {
        return Err(http_format::failed(Failure::BadSignature));
    }
    Ok(Claims {
        tenant: bearer.tenant,
        user: bearer.user,
        expiry: bearer.exp,
    })
}

const REMEMBERED: usize = 4096;

/// Admits the headers of one secret. A header that [`admit`] accepted is remembered by its exact
/// bytes with its claims, and a later request with the same header gets them without a second
/// reading.
pub struct Verifier {
    secret: Vec<u8>,
    accepted: RwLock<HashMap<String, Claims>>,
}

impl Verifier {
    pub fn new(secret: Vec<u8>) -> Self {
        Self {
            secret,
            accepted: RwLock::new(HashMap::new()),
        }
    }

    pub fn admit(&self, header: Option<&str>) -> Result<Claims, Response> {
        let Some(text) = header else {
            return admit(&self.secret, None);
        };
        let known = self
            .accepted
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .get(text)
            .copied();
        if let Some(claims) = known {
            return Ok(claims);
        }
        let claims = admit(&self.secret, header)?;
        let mut accepted = self.accepted.write().unwrap_or_else(|e| e.into_inner());
        if accepted.len() >= REMEMBERED {
            accepted.clear();
        }
        accepted.insert(text.to_owned(), claims);
        Ok(claims)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CLAIMS: Claims = Claims {
        tenant: 12,
        user: 3,
        expiry: 100,
    };

    fn refusal(result: Result<Claims, Response>) -> (u16, String) {
        let response = result.expect_err("the header is refused");
        (
            response.status,
            String::from_utf8(response.body).expect("a body is UTF-8"),
        )
    }

    #[test]
    fn round_trip() {
        let token = issue(b"secret", CLAIMS);
        assert_eq!(
            token,
            "v1.12.3.100.92d8dbd227b10b563128870c7c8bdef0313f9c5ae04a1b121b159d263a14239b"
        );
        assert_eq!(
            admit(b"secret", Some(&format!("Bearer {token}"))).ok(),
            Some(CLAIMS)
        );
    }

    #[test]
    fn verifier_remembers_only_what_it_accepted() {
        let verifier = Verifier::new(b"secret".to_vec());
        let header = format!("Bearer {}", issue(b"secret", CLAIMS));
        assert_eq!(verifier.admit(Some(&header)).ok(), Some(CLAIMS));
        assert_eq!(verifier.admit(Some(&header)).ok(), Some(CLAIMS));
        let forged = header.replacen("v1.12.", "v1.13.", 1);
        let bad = (401, r#"{"error":"bad token signature"}"#.to_owned());
        assert_eq!(refusal(verifier.admit(Some(&forged))), bad);
        assert_eq!(refusal(verifier.admit(Some(&forged))), bad);
    }

    #[test]
    fn rejects() {
        let header = format!("Bearer {}", issue(b"secret", CLAIMS));
        let bad = (401, r#"{"error":"bad token signature"}"#.to_owned());
        assert_eq!(refusal(admit(b"other", Some(&header))), bad);
        let forged = header.replacen("v1.12.", "v1.13.", 1);
        assert_eq!(refusal(admit(b"secret", Some(&forged))), bad);
        let malformed = (401, r#"{"error":"malformed token"}"#.to_owned());
        assert_eq!(
            refusal(admit(b"secret", Some("Bearer v1.012.3.100.00"))),
            malformed
        );
        assert_eq!(
            refusal(admit(b"secret", Some("Bearer v1.12.3.100"))),
            malformed
        );
        assert_eq!(
            refusal(admit(b"secret", None)),
            (
                401,
                r#"{"error":"missing authorization header"}"#.to_owned()
            )
        );
        assert_eq!(
            refusal(admit(b"secret", Some(&header[7..]))),
            (
                401,
                r#"{"error":"authorization is not a bearer token"}"#.to_owned()
            )
        );
    }
}
