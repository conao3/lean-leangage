//! Bearer tokens: `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`, where the tag
//! signs every byte before the last dot. The bytes are written and split by functions generated
//! from `lean/Leanharbor/Token.lean` (`crate::token_format`: `encode_payload`, `join` and
//! `parse_string`); this module computes and compares the tag and checks the expiry. A
//! [`Verifier`] remembers the tokens it accepted, so a token is split and its tag computed once.

use std::collections::HashMap;
use std::sync::RwLock;

use hmac::{Hmac, Mac};
use sha2::Sha256;

use crate::token_format;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Claims {
    pub tenant: u64,
    pub user: u64,
    pub expiry: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenError {
    Malformed,
    BadSignature,
    Expired,
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

/// Accepts a token whose tag matches and whose expiry is not before `now`.
pub fn verify(secret: &[u8], token: &str, now: u64) -> Result<Claims, TokenError> {
    let parsed = token_format::parse_string(token).ok_or(TokenError::Malformed)?;
    mac(secret, &parsed.payload)
        .verify_slice(&parsed.sig)
        .map_err(|_| TokenError::BadSignature)?;
    if parsed.exp < now {
        return Err(TokenError::Expired);
    }
    Ok(Claims {
        tenant: parsed.tenant,
        user: parsed.user,
        expiry: parsed.exp,
    })
}

const REMEMBERED: usize = 4096;

/// Verifies tokens of one secret. A token that [`verify`] accepted is remembered by its exact
/// bytes, and a later request with the same bytes only has its expiry checked.
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

    pub fn verify(&self, token: &str, now: u64) -> Result<Claims, TokenError> {
        let known = self
            .accepted
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .get(token)
            .copied();
        if let Some(claims) = known {
            return if claims.expiry < now {
                Err(TokenError::Expired)
            } else {
                Ok(claims)
            };
        }
        let claims = verify(&self.secret, token, now)?;
        let mut accepted = self.accepted.write().unwrap_or_else(|e| e.into_inner());
        if accepted.len() >= REMEMBERED {
            accepted.clear();
        }
        accepted.insert(token.to_owned(), claims);
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

    #[test]
    fn round_trip() {
        let token = issue(b"secret", CLAIMS);
        assert_eq!(
            token,
            "v1.12.3.100.92d8dbd227b10b563128870c7c8bdef0313f9c5ae04a1b121b159d263a14239b"
        );
        assert_eq!(verify(b"secret", &token, 100), Ok(CLAIMS));
    }

    #[test]
    fn verifier_remembers_only_what_it_accepted() {
        let verifier = Verifier::new(b"secret".to_vec());
        let token = issue(b"secret", CLAIMS);
        assert_eq!(verifier.verify(&token, 100), Ok(CLAIMS));
        assert_eq!(verifier.verify(&token, 100), Ok(CLAIMS));
        assert_eq!(verifier.verify(&token, 101), Err(TokenError::Expired));
        let forged = token.replacen("v1.12.", "v1.13.", 1);
        assert_eq!(verifier.verify(&forged, 0), Err(TokenError::BadSignature));
        assert_eq!(verifier.verify(&forged, 0), Err(TokenError::BadSignature));
        let late = Verifier::new(b"secret".to_vec());
        assert_eq!(late.verify(&token, 101), Err(TokenError::Expired));
        assert_eq!(late.verify(&token, 100), Ok(CLAIMS));
    }

    #[test]
    fn rejects() {
        let token = issue(b"secret", CLAIMS);
        assert_eq!(verify(b"secret", &token, 101), Err(TokenError::Expired));
        assert_eq!(verify(b"other", &token, 0), Err(TokenError::BadSignature));
        let forged = token.replacen("v1.12.", "v1.13.", 1);
        assert_eq!(verify(b"secret", &forged, 0), Err(TokenError::BadSignature));
        assert_eq!(
            verify(b"secret", "v1.012.3.100.00", 0),
            Err(TokenError::Malformed)
        );
        assert_eq!(
            verify(b"secret", "v1.12.3.100", 0),
            Err(TokenError::Malformed)
        );
    }
}
