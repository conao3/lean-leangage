"""Bearer tokens: `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`.

The tag signs every byte before the last dot. The bytes are written by functions generated from
`langs/lean/Leangage/Token.lean` (`leangage.gen.token_format`), and the `Authorization` header is
read by `leangage.gen.http_format.authenticate`, generated from `langs/lean/Leangage/Http.lean`.
This module computes and compares the tag.
"""

import hashlib
import hmac
from dataclasses import dataclass

from leanfran import Err

from leangage.gen import http_format, token_format


@dataclass(frozen=True)
class Claims:
    tenant: int
    user: int
    expiry: int


def _tag(secret: bytes, payload: bytes) -> bytes:
    return hmac.new(secret, payload, hashlib.sha256).digest()


def issue(secret: bytes, claims: Claims) -> str:
    payload = token_format.encodePayload(claims.tenant, claims.user, claims.expiry)
    return bytes(
        token_format.join(payload, list(_tag(secret, bytes(payload))))
    ).decode()


def admit(secret: bytes, header: str | None) -> Claims | http_format.Response:
    """The claims of the token in the `Authorization` header when its tag is the HMAC of its
    payload, or the answer to the request. The expiry is checked by the kernel's `request`."""
    read = http_format.authenticate(header)
    if isinstance(read, Err):
        return read.error
    bearer = read.value
    if not hmac.compare_digest(_tag(secret, bytes(bearer.payload)), bytes(bearer.sig)):
        return http_format.failed(http_format.Failure.badSignature)
    return Claims(bearer.tenant, bearer.user, bearer.exp)


class Verifier:
    """Admits the headers of one secret.

    A header that `admit` accepted is remembered by its exact text with its claims, and a later
    request with the same header gets them without a second reading.
    """

    REMEMBERED = 4096

    def __init__(self, secret: bytes) -> None:
        self._secret = secret
        self._accepted: dict[str, Claims] = {}

    def admit(self, header: str | None) -> Claims | http_format.Response:
        if header is None:
            return admit(self._secret, None)
        claims = self._accepted.get(header)
        if claims is not None:
            return claims
        answer = admit(self._secret, header)
        if isinstance(answer, Claims):
            if len(self._accepted) >= self.REMEMBERED:
                self._accepted.clear()
            self._accepted[header] = answer
        return answer
