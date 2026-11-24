"""Bearer tokens: `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`.

The tag signs every byte before the last dot.
"""

import hashlib
import hmac
import re
from dataclasses import dataclass

_DECIMAL = re.compile(r"0|[1-9][0-9]*")
_HEX = re.compile(r"(?:[0-9a-f]{2})*")


@dataclass(frozen=True)
class Claims:
    tenant: int
    user: int
    expiry: int


class TokenError(Exception):
    pass


def _tag(secret: bytes, payload: str) -> bytes:
    return hmac.new(secret, payload.encode(), hashlib.sha256).digest()


def issue(secret: bytes, claims: Claims) -> str:
    payload = f"v1.{claims.tenant}.{claims.user}.{claims.expiry}"
    return f"{payload}.{_tag(secret, payload).hex()}"


def _decimal(text: str) -> int:
    if not _DECIMAL.fullmatch(text) or int(text) >= 2**64:
        raise TokenError("malformed token")
    return int(text)


def verify(secret: bytes, token: str, now: int) -> Claims:
    """Accepts a token whose tag matches and whose expiry is not before `now`."""
    payload, dot, tag = token.rpartition(".")
    parts = payload.split(".")
    if not dot or len(parts) != 4 or parts[0] != "v1" or not _HEX.fullmatch(tag):
        raise TokenError("malformed token")
    claims = Claims(_decimal(parts[1]), _decimal(parts[2]), _decimal(parts[3]))
    if not hmac.compare_digest(_tag(secret, payload), bytes.fromhex(tag)):
        raise TokenError("bad token signature")
    if claims.expiry < now:
        raise TokenError("token expired")
    return claims
