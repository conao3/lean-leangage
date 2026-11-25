// Command bytes-bench times the byte functions the shells call on every request: (a) the check of one
// token (split and HMAC), (b) the bytes of one calculator reply and (c) the bytes of a notes list
// of 20 notes with bodies of 200 bytes.
package main

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"fmt"
	"slices"
	"strings"
	"time"

	"github.com/conao3/lean-leanharbor/go/calculator"
	"github.com/conao3/lean-leanharbor/go/calculator/kernel"
	"github.com/conao3/lean-leanharbor/go/leanharbor"
	"github.com/conao3/lean-leanharbor/go/leanharbor/jsonformat"
	"github.com/conao3/lean-leanharbor/go/leanharbor/token"
)

const rounds = 5

var sink any

func measure(label string, iterations int, f func()) {
	perOp := make([]float64, rounds)
	for r := range perOp {
		start := time.Now()
		for range iterations {
			f()
		}
		perOp[r] = float64(time.Since(start).Nanoseconds()) / float64(iterations)
	}
	slices.Sort(perOp)
	fmt.Printf("%-28s median %10.0f ns  min %10.0f ns\n", label, perOp[rounds/2], perOp[0])
}

// notesToks are the tokens of {"notes":[...]} for 20 notes, in the order the Rust notes shell
// writes their members.
func notesToks() []jsonformat.Tok {
	body := []byte(strings.Repeat("n", 200))
	out := []jsonformat.Tok{jsonformat.TokObjOpen{}, jsonformat.TokKey{S: []byte("notes")}, jsonformat.TokArrOpen{}}
	for i := range uint64(20) {
		out = append(out,
			jsonformat.TokObjOpen{},
			jsonformat.TokKey{S: []byte("body")}, jsonformat.TokStr{S: body},
			jsonformat.TokKey{S: []byte("id")}, jsonformat.TokNum{N: i},
			jsonformat.TokKey{S: []byte("owner")}, jsonformat.TokNum{N: 7},
			jsonformat.TokKey{S: []byte("shared")}, jsonformat.TokBool{B: i%2 == 0},
			jsonformat.TokObjClose{},
		)
	}
	return append(out, jsonformat.TokArrClose{}, jsonformat.TokObjClose{})
}

func main() {
	secret := []byte("bench-secret")
	claims := leanharbor.Claims{Tenant: 1, User: 42, Expiry: 4_102_444_800}
	tok := leanharbor.Issue(secret, claims)
	measure("(a) token verify", 100_000, func() {
		got, err := leanharbor.Verify(secret, tok, 0)
		if err != nil || got != claims {
			panic("a valid token")
		}
	})
	measure("    split only", 100_000, func() { sink = token.Parse([]byte(tok)) })
	payload := []byte(tok[:strings.LastIndexByte(tok, '.')])
	measure("    HMAC only", 100_000, func() {
		mac := hmac.New(sha256.New, secret)
		mac.Write(payload)
		sink = mac.Sum(nil)
	})

	reply := kernel.Reply{V: 6}
	measure("(b) calculator reply", 100_000, func() { sink = calculator.Calculator{}.EncodeReply(reply) })

	toks := notesToks()
	body, err := jsonformat.Write(toks)
	if err != nil || !bytes.HasPrefix(body, []byte(`{"notes":[{"body":"nnn`)) {
		panic("the notes list")
	}
	measure("(c) notes list of 20", 1_000, func() {
		out, err := jsonformat.Write(notesToks())
		if err != nil {
			panic(err)
		}
		sink = out
	})
}
