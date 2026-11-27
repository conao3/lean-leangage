package leangage

import (
	"crypto/hmac"
	"crypto/sha256"
	"errors"
	"sync"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/langs/go/leangage/gen/httpformat"
	"github.com/conao3/lean-leangage/langs/go/leangage/gen/token"
)

// Claims are what a bearer token states. A token is
// `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`, where the tag signs every byte
// before the last dot. The bytes are written by functions generated from
// `langs/lean/Leangage/Token.lean` (package token), and the `Authorization` header is read by
// httpformat.Authenticate, generated from `langs/lean/Leangage/Http.lean`. This file computes and
// compares the tag.
type Claims struct {
	Tenant uint64
	User   uint64
	Expiry uint64
}

func tag(secret []byte, payload []byte) []byte {
	mac := hmac.New(sha256.New, secret)
	mac.Write(payload)
	return mac.Sum(nil)
}

func Issue(secret []byte, claims Claims) string {
	payload := token.EncodePayload(claims.Tenant, claims.User, claims.Expiry)
	return string(token.Join(payload, tag(secret, payload)))
}

// Admit is the claims of the token in the `Authorization` header when its tag is the HMAC of
// its payload, or the answer to the request. A nil header is a request without one. The expiry
// is checked by the kernel's Request.
func Admit(secret []byte, header *string) (Claims, *httpformat.Response) {
	bearer, err := httpformat.Authenticate(header)
	if answer, ok := errors.AsType[*leanfran.ExceptError[httpformat.Response]](err); ok {
		return Claims{}, &answer.Value
	}
	if err != nil {
		panic(err)
	}
	if !hmac.Equal(tag(secret, bearer.Payload), bearer.Sig) {
		answer := httpformat.Failed(httpformat.FailureBadSignature())
		return Claims{}, &answer
	}
	return Claims{Tenant: bearer.Tenant, User: bearer.User, Expiry: bearer.Exp}, nil
}

const remembered = 4096

// Verifier admits the headers of one secret. A header that Admit accepted is remembered by its
// exact bytes with its claims, and a later request with the same header gets them without a
// second reading.
type Verifier struct {
	secret   []byte
	mu       sync.RWMutex
	accepted map[string]Claims
}

func NewVerifier(secret []byte) *Verifier {
	return &Verifier{secret: secret, accepted: map[string]Claims{}}
}

func (v *Verifier) Admit(header *string) (Claims, *httpformat.Response) {
	if header == nil {
		return Admit(v.secret, nil)
	}
	v.mu.RLock()
	claims, known := v.accepted[*header]
	v.mu.RUnlock()
	if known {
		return claims, nil
	}
	claims, answer := Admit(v.secret, header)
	if answer != nil {
		return Claims{}, answer
	}
	v.mu.Lock()
	if len(v.accepted) >= remembered {
		clear(v.accepted)
	}
	v.accepted[*header] = claims
	v.mu.Unlock()
	return claims, nil
}
