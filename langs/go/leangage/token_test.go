package leangage

import (
	"strings"
	"testing"

	"github.com/conao3/lean-leangage/langs/go/leangage/gen/httpformat"
)

var claims = Claims{Tenant: 12, User: 3, Expiry: 100}

// The token the Rust and the Python servers issue for the same secret and claims.
const shared = "v1.12.3.100.92d8dbd227b10b563128870c7c8bdef0313f9c5ae04a1b121b159d263a14239b"

const (
	badSignature = `401 {"error":"bad token signature"}`
	malformed    = `401 {"error":"malformed token"}`
)

func refusal(answer *httpformat.Response) string {
	if answer == nil {
		return "accepted"
	}
	return strings.Join([]string{itoa(answer.Status), string(answer.Body)}, " ")
}

func itoa(status uint16) string {
	return string([]byte{byte('0' + status/100), byte('0' + status/10%10), byte('0' + status%10)})
}

func TestRoundTrip(t *testing.T) {
	token := Issue([]byte("secret"), claims)
	if token != shared {
		t.Fatalf("issued %s", token)
	}
	header := "Bearer " + token
	got, answer := Admit([]byte("secret"), &header)
	if answer != nil || got != claims {
		t.Fatalf("got %v, %v", got, refusal(answer))
	}
}

func TestRejects(t *testing.T) {
	token := Issue([]byte("secret"), claims)
	cases := []struct {
		secret string
		header string
		want   string
	}{
		{"other", "Bearer " + token, badSignature},
		{"secret", "Bearer " + strings.Replace(token, "v1.12.", "v1.13.", 1), badSignature},
		{"secret", "Bearer v1.12.3.100.", badSignature},
		{"secret", "Bearer v1.12.3.100.00", badSignature},
		{"secret", "Bearer v1.012.3.100.00", malformed},
		{"secret", "Bearer v1.12.3.100", malformed},
		{"secret", "Bearer v1.12.3.18446744073709551616.00", malformed},
		{"secret", "Bearer v2.12.3.100.00", malformed},
		{"secret", "Bearer " + token[:12] + strings.ToUpper(token[12:]), malformed},
		{"secret", "Bearer v1.12.3.100.0", malformed},
		{"secret", "Bearer ", malformed},
		{"secret", token, `401 {"error":"authorization is not a bearer token"}`},
	}
	for _, c := range cases {
		if _, answer := Admit([]byte(c.secret), &c.header); refusal(answer) != c.want {
			t.Errorf("%q: got %v, want %v", c.header, refusal(answer), c.want)
		}
	}
	if _, answer := Admit([]byte("secret"), nil); refusal(answer) != `401 {"error":"missing authorization header"}` {
		t.Errorf("no header: got %v", refusal(answer))
	}
}

func TestVerifierRemembersOnlyWhatItAccepted(t *testing.T) {
	claims := Claims{Tenant: 12, User: 3, Expiry: 100}
	header := "Bearer " + Issue([]byte("secret"), claims)
	verifier := NewVerifier([]byte("secret"))
	for range 2 {
		if got, answer := verifier.Admit(&header); answer != nil || got != claims {
			t.Fatalf("got %v, %v", got, refusal(answer))
		}
	}
	forged := strings.Replace(header, "v1.12.", "v1.13.", 1)
	for range 2 {
		if _, answer := verifier.Admit(&forged); refusal(answer) != badSignature {
			t.Fatalf("got %v", refusal(answer))
		}
	}
}
