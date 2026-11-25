//! Bearer tokens: `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`, where the tag
//! signs every byte before the last dot. The bytes are written and split by functions generated
//! from `lean/Leanharbor/Token.lean` (`crate::token_format`); this module computes and compares
//! the tag and checks the expiry.

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
    let parsed = token_format::parse(token.as_bytes().to_vec()).ok_or(TokenError::Malformed)?;
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
