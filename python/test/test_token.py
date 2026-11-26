from leangage import Claims, Verifier, admit, issue

CLAIMS = Claims(tenant=12, user=3, expiry=100)

BAD_SIGNATURE = (401, b'{"error":"bad token signature"}')
MALFORMED = (401, b'{"error":"malformed token"}')


def refusal(answer) -> tuple[int, bytes]:
    assert not isinstance(answer, Claims)
    return answer.status, bytes(answer.body)


def test_round_trip() -> None:
    token = issue(b"secret", CLAIMS)
    assert token == (
        "v1.12.3.100.92d8dbd227b10b563128870c7c8bdef0313f9c5ae04a1b121b159d263a14239b"
    )
    assert admit(b"secret", f"Bearer {token}") == CLAIMS


def test_rejects() -> None:
    token = issue(b"secret", CLAIMS)
    assert refusal(admit(b"other", f"Bearer {token}")) == BAD_SIGNATURE
    forged = token.replace("v1.12.", "v1.13.", 1)
    assert refusal(admit(b"secret", f"Bearer {forged}")) == BAD_SIGNATURE
    assert refusal(admit(b"secret", "Bearer v1.012.3.100.00")) == MALFORMED
    assert refusal(admit(b"secret", "Bearer v1.12.3.100")) == MALFORMED
    assert refusal(admit(b"secret", None)) == (
        401,
        b'{"error":"missing authorization header"}',
    )
    assert refusal(admit(b"secret", token)) == (
        401,
        b'{"error":"authorization is not a bearer token"}',
    )


def test_verifier_remembers_only_what_it_accepted() -> None:
    verifier = Verifier(b"secret")
    header = f"Bearer {issue(b'secret', CLAIMS)}"
    assert verifier.admit(header) == CLAIMS
    assert verifier.admit(header) == CLAIMS
    forged = header.replace("v1.12.", "v1.13.", 1)
    for _ in range(2):
        assert refusal(verifier.admit(forged)) == BAD_SIGNATURE
