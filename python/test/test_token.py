import pytest
from leanharbor import Claims, TokenError, issue, verify

CLAIMS = Claims(tenant=12, user=3, expiry=100)


def test_round_trip() -> None:
    token = issue(b"secret", CLAIMS)
    assert token == (
        "v1.12.3.100.92d8dbd227b10b563128870c7c8bdef0313f9c5ae04a1b121b159d263a14239b"
    )
    assert verify(b"secret", token, 100) == CLAIMS


@pytest.mark.parametrize(
    ("secret", "edit", "now"),
    [
        (b"secret", lambda t: t, 101),
        (b"other", lambda t: t, 0),
        (b"secret", lambda t: t.replace("v1.12.", "v1.13.", 1), 0),
        (b"secret", lambda t: "v1.012.3.100.00", 0),
        (b"secret", lambda t: "v1.12.3.100", 0),
    ],
)
def test_rejects(secret: bytes, edit, now: int) -> None:
    with pytest.raises(TokenError):
        verify(secret, edit(issue(b"secret", CLAIMS)), now)
