package leanharbor

import (
	"strings"
	"testing"
)

var claims = Claims{Tenant: 12, User: 3, Expiry: 100}

// The token the Rust and the Python shells issue for the same secret and claims.
const shared = "v1.12.3.100.92d8dbd227b10b563128870c7c8bdef0313f9c5ae04a1b121b159d263a14239b"

func TestRoundTrip(t *testing.T) {
	token := Issue([]byte("secret"), claims)
	if token != shared {
		t.Fatalf("issued %s", token)
	}
	got, err := Verify([]byte("secret"), token, 100)
	if err != nil || got != claims {
		t.Fatalf("got %v, %v", got, err)
	}
}

func TestRejects(t *testing.T) {
	token := Issue([]byte("secret"), claims)
	cases := []struct {
		secret string
		token  string
		now    uint64
		want   error
	}{
		{"secret", token, 101, ErrTokenExpired},
		{"other", token, 0, ErrTokenBadSignature},
		{"secret", strings.Replace(token, "v1.12.", "v1.13.", 1), 0, ErrTokenBadSignature},
		{"secret", "v1.12.3.100.", 0, ErrTokenBadSignature},
		{"secret", "v1.12.3.100.00", 0, ErrTokenBadSignature},
		{"secret", "v1.012.3.100.00", 0, ErrTokenMalformed},
		{"secret", "v1.12.3.100", 0, ErrTokenMalformed},
		{"secret", "v1.12.3.18446744073709551616.00", 0, ErrTokenMalformed},
		{"secret", "v2.12.3.100.00", 0, ErrTokenMalformed},
		{"secret", token[:12] + strings.ToUpper(token[12:]), 0, ErrTokenMalformed},
		{"secret", "v1.12.3.100.0", 0, ErrTokenMalformed},
		{"secret", "", 0, ErrTokenMalformed},
	}
	for _, c := range cases {
		if _, err := Verify([]byte(c.secret), c.token, c.now); err != c.want {
			t.Errorf("%q at %d: got %v, want %v", c.token, c.now, err, c.want)
		}
	}
}
