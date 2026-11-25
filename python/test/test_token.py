import pytest
from leanharbor import Claims, TokenError, Verifier, issue, verify

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


def test_verifier_remembers_only_what_it_accepted() -> None:
    verifier = Verifier(b"secret")
    token = issue(b"secret", CLAIMS)
    assert verifier.verify(token, 100) == CLAIMS
    assert verifier.verify(token, 100) == CLAIMS
    with pytest.raises(TokenError, match="expired"):
        verifier.verify(token, 101)
    forged = token.replace("v1.12.", "v1.13.", 1)
    for _ in range(2):
        with pytest.raises(TokenError, match="signature"):
            verifier.verify(forged, 0)
    late = Verifier(b"secret")
    with pytest.raises(TokenError, match="expired"):
        late.verify(token, 101)
    assert late.verify(token, 100) == CLAIMS
