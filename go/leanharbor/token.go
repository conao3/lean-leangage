package leanharbor

import (
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"strconv"
	"strings"
)

// Claims are what a bearer token states. A token is
// `v1.<tenant>.<user>.<expiry unix seconds>.<hex hmac-sha256>`, where the tag signs every byte
// before the last dot.
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

func tag(secret []byte, payload string) []byte {
	mac := hmac.New(sha256.New, secret)
	mac.Write([]byte(payload))
	return mac.Sum(nil)
}

func Issue(secret []byte, claims Claims) string {
	payload := fmt.Sprintf("v1.%d.%d.%d", claims.Tenant, claims.User, claims.Expiry)
	return payload + "." + hex.EncodeToString(tag(secret, payload))
}

func decimal(s string) (uint64, bool) {
	if s == "" || (s != "0" && s[0] == '0') {
		return 0, false
	}
	for _, b := range []byte(s) {
		if b < '0' || b > '9' {
			return 0, false
		}
	}
	n, err := strconv.ParseUint(s, 10, 64)
	return n, err == nil
}

func unhex(s string) ([]byte, bool) {
	if s != strings.ToLower(s) {
		return nil, false
	}
	out, err := hex.DecodeString(s)
	return out, err == nil
}

// Verify accepts a token whose tag matches and whose expiry is not before now.
func Verify(secret []byte, token string, now uint64) (Claims, error) {
	dot := strings.LastIndexByte(token, '.')
	if dot < 0 {
		return Claims{}, ErrTokenMalformed
	}
	payload := token[:dot]
	parts := strings.Split(payload, ".")
	if len(parts) != 4 || parts[0] != "v1" {
		return Claims{}, ErrTokenMalformed
	}
	tenant, okTenant := decimal(parts[1])
	user, okUser := decimal(parts[2])
	expiry, okExpiry := decimal(parts[3])
	signature, okSignature := unhex(token[dot+1:])
	if !okTenant || !okUser || !okExpiry || !okSignature {
		return Claims{}, ErrTokenMalformed
	}
	if !hmac.Equal(tag(secret, payload), signature) {
		return Claims{}, ErrTokenBadSignature
	}
	if expiry < now {
		return Claims{}, ErrTokenExpired
	}
	return Claims{Tenant: tenant, User: user, Expiry: expiry}, nil
}
