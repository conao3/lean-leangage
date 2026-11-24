//! Bearer tokens: `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`, where the tag
//! signs every byte before the last dot.

use hmac::{Hmac, Mac};
use sha2::Sha256;

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

fn mac(secret: &[u8], payload: &str) -> Hmac<Sha256> {
    let mut mac = Hmac::<Sha256>::new_from_slice(secret).expect("HMAC takes a key of any length");
    mac.update(payload.as_bytes());
    mac
}

pub fn issue(secret: &[u8], claims: Claims) -> String {
    let payload = format!("v1.{}.{}.{}", claims.tenant, claims.user, claims.expiry);
    let tag = mac(secret, &payload).finalize().into_bytes();
    let hex: String = tag.iter().map(|b| format!("{b:02x}")).collect();
    format!("{payload}.{hex}")
}

fn decimal(s: &str) -> Option<u64> {
    let canonical =
        !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) && (s == "0" || !s.starts_with('0'));
    if canonical { s.parse().ok() } else { None }
}

fn unhex(s: &str) -> Option<Vec<u8>> {
    let digit = |b: u8| match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        _ => None,
    };
    let bytes = s.as_bytes();
    if !bytes.len().is_multiple_of(2) {
        return None;
    }
    bytes
        .chunks(2)
        .map(|pair| Some(digit(pair[0])? << 4 | digit(pair[1])?))
        .collect()
}

/// Accepts a token whose tag matches and whose expiry is not before `now`.
pub fn verify(secret: &[u8], token: &str, now: u64) -> Result<Claims, TokenError> {
    let (payload, hex) = token.rsplit_once('.').ok_or(TokenError::Malformed)?;
    let parts: Vec<&str> = payload.split('.').collect();
    let [version, tenant, user, expiry] = parts[..] else {
        return Err(TokenError::Malformed);
    };
    if version != "v1" {
        return Err(TokenError::Malformed);
    }
    let claims = Claims {
        tenant: decimal(tenant).ok_or(TokenError::Malformed)?,
        user: decimal(user).ok_or(TokenError::Malformed)?,
        expiry: decimal(expiry).ok_or(TokenError::Malformed)?,
    };
    let tag = unhex(hex).ok_or(TokenError::Malformed)?;
    mac(secret, payload)
        .verify_slice(&tag)
        .map_err(|_| TokenError::BadSignature)?;
    if claims.expiry < now {
        return Err(TokenError::Expired);
    }
    Ok(claims)
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
        assert!(token.starts_with("v1.12.3.100."));
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
