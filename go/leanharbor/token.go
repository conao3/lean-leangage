package leanharbor

import (
	"crypto/hmac"
	"crypto/sha256"
	"errors"
	"sync"

	"github.com/conao3/lean-leanharbor/go/leanharbor/token"
)

// Claims are what a bearer token states. A token is
// `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`, where the tag signs every byte
// before the last dot. The bytes are written and split by functions generated from
// `lean/Leanharbor/Token.lean` (package token); this file computes and compares the tag and checks
// the expiry.
type Claims struct {
	Tenant uint64
	User   uint64
	Expiry uint64
}

var (
	ErrTokenMalformed    = errors.New("malformed token")
	ErrTokenBadSignature = errors.New("bad token signature")
	ErrTokenExpired      = errors.New("token expired")
)

func tag(secret []byte, payload []byte) []byte {
	mac := hmac.New(sha256.New, secret)
	mac.Write(payload)
	return mac.Sum(nil)
}

func Issue(secret []byte, claims Claims) string {
	payload := token.EncodePayload(claims.Tenant, claims.User, claims.Expiry)
	return string(token.Join(payload, tag(secret, payload)))
}

// Verify accepts a token whose tag matches and whose expiry is not before now.
func Verify(secret []byte, tok string, now uint64) (Claims, error) {
	parsed, err := token.ParseString(tok)
	if err != nil || parsed == nil {
		return Claims{}, ErrTokenMalformed
	}
	if !hmac.Equal(tag(secret, parsed.Payload), parsed.Sig) {
		return Claims{}, ErrTokenBadSignature
	}
	if parsed.Exp < now {
		return Claims{}, ErrTokenExpired
	}
	return Claims{Tenant: parsed.Tenant, User: parsed.User, Expiry: parsed.Exp}, nil
}

const remembered = 4096

// Verifier verifies tokens of one secret. A token that Verify accepted is remembered by its
// exact bytes, and a later request with the same bytes only has its expiry checked.
type Verifier struct {
	secret   []byte
	mu       sync.RWMutex
	accepted map[string]Claims
}

func NewVerifier(secret []byte) *Verifier {
	return &Verifier{secret: secret, accepted: map[string]Claims{}}
}

func (v *Verifier) Verify(tok string, now uint64) (Claims, error) {
	v.mu.RLock()
	claims, known := v.accepted[tok]
	v.mu.RUnlock()
	if known {
		if claims.Expiry < now {
			return Claims{}, ErrTokenExpired
		}
		return claims, nil
	}
	claims, err := Verify(v.secret, tok, now)
	if err != nil {
		return Claims{}, err
	}
	v.mu.Lock()
	if len(v.accepted) >= remembered {
		clear(v.accepted)
	}
	v.accepted[tok] = claims
	v.mu.Unlock()
	return claims, nil
}
