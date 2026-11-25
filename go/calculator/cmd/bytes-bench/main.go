// Command bytes-bench times the byte functions the shells call on every request: (a) the check of
// one token (split and HMAC), (b) the bytes of one calculator reply and (c) the bytes of a notes
// list of 20 notes with bodies of 200 bytes. Each line times the functions over lists (Parse,
// EncodeReply, Write) and the functions the shells call (ParseString, EncodeReplyArray,
// WriteArray) in alternating rounds.
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

const rounds = 7

var sink any

func perOp(iterations int, f func()) float64 {
	start := time.Now()
	for range iterations {
		f()
	}
	return float64(time.Since(start).Nanoseconds()) / float64(iterations)
}

func show(perOp []float64) string {
	slices.Sort(perOp)
	return fmt.Sprintf("%10.0f ns (median %10.0f)", perOp[0], perOp[rounds/2])
}

// compare prints the minimum and the median of the rounds, lists first.
func compare(label string, iterations int, lists, arrays func()) {
	var old, new []float64
	for range rounds {
		old = append(old, perOp(iterations, lists))
		new = append(new, perOp(iterations, arrays))
	}
	fmt.Printf("%-22s lists %s  arrays %s\n", label, show(old), show(new))
}

func tag(secret, payload []byte) []byte {
	mac := hmac.New(sha256.New, secret)
	mac.Write(payload)
	return mac.Sum(nil)
}

// verifyLists is leanharbor.Verify with Parse in place of ParseString.
func verifyLists(secret []byte, tok string, now uint64) (leanharbor.Claims, bool) {
	parsed := token.Parse([]byte(tok))
	if parsed == nil || !hmac.Equal(tag(secret, parsed.Payload), parsed.Sig) || parsed.Exp < now {
		return leanharbor.Claims{}, false
	}
	return leanharbor.Claims{Tenant: parsed.Tenant, User: parsed.User, Expiry: parsed.Exp}, true
}

type note struct {
	id, owner uint64
	shared    bool
	body      string
}

var notes = func() []note {
	out := make([]note, 20)
	for i := range out {
		out[i] = note{id: uint64(i), owner: 7, shared: i%2 == 0, body: strings.Repeat("n", 200)}
	}
	return out
}()

// notesToks are the tokens of {"notes":[...]}, in the order the Rust notes shell writes their
// members, over lists.
func notesToks() []jsonformat.Tok {
	key := func(s string) jsonformat.Tok { return jsonformat.TokKey{S: []byte(s)} }
	out := []jsonformat.Tok{jsonformat.TokObjOpen{}, key("notes"), jsonformat.TokArrOpen{}}
	for _, n := range notes {
		out = append(out,
			jsonformat.TokObjOpen{},
			key("body"), jsonformat.TokStr{S: []byte(n.body)},
			key("id"), jsonformat.TokNum{N: n.id},
			key("owner"), jsonformat.TokNum{N: n.owner},
			key("shared"), jsonformat.TokBool{B: n.shared},
			jsonformat.TokObjClose{},
		)
	}
	return append(out, jsonformat.TokArrClose{}, jsonformat.TokObjClose{})
}

// notesStrToks are the same tokens, with strings.
func notesStrToks() []jsonformat.StrTok {
	key := func(s string) jsonformat.StrTok { return jsonformat.StrTokKey{S: s} }
	out := []jsonformat.StrTok{jsonformat.StrTokObjOpen{}, key("notes"), jsonformat.StrTokArrOpen{}}
	for _, n := range notes {
		out = append(out,
			jsonformat.StrTokObjOpen{},
			key("body"), jsonformat.StrTokStr{S: n.body},
			key("id"), jsonformat.StrTokNum{N: n.id},
			key("owner"), jsonformat.StrTokNum{N: n.owner},
			key("shared"), jsonformat.StrTokBool{B: n.shared},
			jsonformat.StrTokObjClose{},
		)
	}
	return append(out, jsonformat.StrTokArrClose{}, jsonformat.StrTokObjClose{})
}

func must[T any](value T, err error) T {
	if err != nil {
		panic(err)
	}
	return value
}

func main() {
	secret := []byte("bench-secret")
	claims := leanharbor.Claims{Tenant: 1, User: 42, Expiry: 4_102_444_800}
	tok := leanharbor.Issue(secret, claims)
	if got, ok := verifyLists(secret, tok, 0); !ok || got != claims {
		panic("a valid token over lists")
	}
	if got, err := leanharbor.Verify(secret, tok, 0); err != nil || got != claims {
		panic("a valid token")
	}
	compare("(a) token check", 100_000,
		func() { sink, _ = verifyLists(secret, tok, 0) },
		func() { sink, _ = leanharbor.Verify(secret, tok, 0) })
	compare("    split only", 100_000,
		func() { sink = token.Parse([]byte(tok)) },
		func() { sink = must(token.ParseString(tok)) })
	payload := []byte(tok[:strings.LastIndexByte(tok, '.')])
	var hmacOnly []float64
	for range rounds {
		hmacOnly = append(hmacOnly, perOp(100_000, func() { sink = tag(secret, payload) }))
	}
	fmt.Printf("    HMAC only               %s\n", show(hmacOnly))

	reply := kernel.Reply{V: 6}
	if !bytes.Equal(kernel.EncodeReply(reply), calculator.Calculator{}.EncodeReply(reply)) {
		panic("the calculator reply")
	}
	compare("(b) calculator reply", 100_000,
		func() { sink = kernel.EncodeReply(reply) },
		func() { sink = calculator.Calculator{}.EncodeReply(reply) })

	body := must(jsonformat.Write(notesToks()))
	if !bytes.Equal(body, must(jsonformat.WriteArray(notesStrToks()))) ||
		!bytes.HasPrefix(body, []byte(`{"notes":[{"body":"nnn`)) {
		panic("the notes list")
	}
	compare("(c) notes list of 20", 500,
		func() { sink = must(jsonformat.Write(notesToks())) },
		func() { sink = must(jsonformat.WriteArray(notesStrToks())) })
}
