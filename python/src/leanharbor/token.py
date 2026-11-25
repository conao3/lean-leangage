"""Bearer tokens: `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`.

The tag signs every byte before the last dot. The bytes are written and split by functions
generated from `lean/Leanharbor/Token.lean` (`leanharbor.token_format`); this module computes and
compares the tag and checks the expiry.
"""

import hashlib
import hmac
from dataclasses import dataclass

from leanharbor import token_format


@dataclass(frozen=True)
class Claims:
    tenant: int
    user: int
    expiry: int


class TokenError(Exception):
    pass


def _tag(secret: bytes, payload: bytes) -> bytes:
    return hmac.new(secret, payload, hashlib.sha256).digest()


def issue(secret: bytes, claims: Claims) -> str:
    payload = token_format.encodePayload(claims.tenant, claims.user, claims.expiry)
    return bytes(
        token_format.join(payload, list(_tag(secret, bytes(payload))))
    ).decode()


def verify(secret: bytes, token: str, now: int) -> Claims:
    """Accepts a token whose tag matches and whose expiry is not before `now`."""
    parsed = token_format.parse(list(token.encode()))
    if parsed is None:
        raise TokenError("malformed token")
    if not hmac.compare_digest(_tag(secret, bytes(parsed.payload)), bytes(parsed.sig)):
        raise TokenError("bad token signature")
    if parsed.exp < now:
        raise TokenError("token expired")
    return Claims(parsed.tenant, parsed.user, parsed.exp)
