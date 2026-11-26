// Command bytes-bench times the byte functions the servers call on every request: (a) the check of
// one token (split and HMAC), (b) the bytes of one calculator reply and (c) the bytes of a notes
// list of 20 notes with bodies of 200 bytes. Each line times the functions over lists (Parse,
// EncodeReply, Write) and the functions over strings and arrays (Authenticate, EncodeReplyArray,
// WriteArray) in alternating rounds. (d) times the reading of one request body into a command,
// written without a space and with a space after each colon and comma, and (e) the answer to an accepted command, each written by hand with encoding/json and as the
// calculator server does it: the tokens of leangage.BodyOf given to the generated wire.Request, and
// the generated wire.Respond.
package main

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"slices"
	"strconv"
	"strings"
	"time"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/go/calculator/kernel"
	"github.com/conao3/lean-leangage/go/calculator/wire"
	"github.com/conao3/lean-leangage/go/leangage"
	"github.com/conao3/lean-leangage/go/leangage/httpformat"
	"github.com/conao3/lean-leangage/go/leangage/jsonformat"
	"github.com/conao3/lean-leangage/go/leangage/token"
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
	compareAs(label, "lists", "arrays", iterations, lists, arrays)
}

// compareAs prints the minimum and the median of the rounds of the two, named first and second.
func compareAs(label, first, second string, iterations int, lists, arrays func()) {
	var old, new []float64
	for range rounds {
		old = append(old, perOp(iterations, lists))
		new = append(new, perOp(iterations, arrays))
	}
	fmt.Printf("%-22s %s %s  %s %s\n", label, first, show(old), second, show(new))
}

func tag(secret, payload []byte) []byte {
	mac := hmac.New(sha256.New, secret)
	mac.Write(payload)
	return mac.Sum(nil)
}

// verifyLists is the check of a token with Parse, the tag and the expiry, written by hand.
func verifyLists(secret []byte, tok string, now uint64) (leangage.Claims, bool) {
	parsed := token.Parse([]byte(tok))
	if parsed == nil || !hmac.Equal(tag(secret, parsed.Payload), parsed.Sig) || parsed.Exp < now {
		return leangage.Claims{}, false
	}
	return leangage.Claims{Tenant: parsed.Tenant, User: parsed.User, Expiry: parsed.Exp}, true
}

// decodeByHand reads a body into a command with encoding/json, written by hand.
func decodeByHand(body []byte) kernel.Command {
	var fields map[string]json.RawMessage
	if err := json.Unmarshal(body, &fields); err != nil || fields == nil {
		return nil
	}
	var name string
	if json.Unmarshal(fields["cmd"], &name) != nil {
		return nil
	}
	number := func(field string) (uint64, bool) {
		value, err := strconv.ParseUint(string(fields[field]), 10, 64)
		return value, err == nil
	}
	switch {
	case name == "set" && len(fields) == 2:
		if value, ok := number("value"); ok {
			return kernel.CommandSet{Value: value}
		}
	case name == "apply" && len(fields) == 3:
		var op string
		if json.Unmarshal(fields["op"], &op) != nil {
			return nil
		}
		ops := map[string]kernel.Op{
			"add": kernel.OpAdd(), "sub": kernel.OpSub(), "mul": kernel.OpMul(), "div": kernel.OpDiv(),
		}
		if arg, ok := number("arg"); ok {
			if found, ok := ops[op]; ok {
				return kernel.CommandApply{Op: found, Arg: arg}
			}
		}
	case name == "get" && len(fields) == 1:
		return kernel.CommandGet{}
	}
	return nil
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

// notesToks are the tokens of {"notes":[...]}, in the order the Rust notes server writes their
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
	claims := leangage.Claims{Tenant: 1, User: 42, Expiry: 4_102_444_800}
	tok := leangage.Issue(secret, claims)
	if got, ok := verifyLists(secret, tok, 0); !ok || got != claims {
		panic("a valid token over lists")
	}
	header := "Bearer " + tok
	if got, answer := leangage.Admit(secret, &header); answer != nil || got != claims {
		panic("a valid token")
	}
	compare("(a) token check", 100_000,
		func() { sink, _ = verifyLists(secret, tok, 0) },
		func() { sink, _ = leangage.Admit(secret, &header) })
	compare("    split only", 100_000,
		func() { sink = token.Parse([]byte(tok)) },
		func() { sink = must(httpformat.Authenticate(&header)) })
	payload := []byte(tok[:strings.LastIndexByte(tok, '.')])
	var hmacOnly []float64
	for range rounds {
		hmacOnly = append(hmacOnly, perOp(100_000, func() { sink = tag(secret, payload) }))
	}
	fmt.Printf("    HMAC only               %s\n", show(hmacOnly))

	reply := kernel.Reply{V: 6}
	if !bytes.Equal(kernel.EncodeReply(reply), kernel.EncodeReplyArray(reply)) {
		panic("the calculator reply")
	}
	compare("(b) calculator reply", 100_000,
		func() { sink = kernel.EncodeReply(reply) },
		func() { sink = kernel.EncodeReplyArray(reply) })

	body := must(jsonformat.Write(notesToks()))
	if !bytes.Equal(body, must(jsonformat.WriteArray(notesStrToks()))) ||
		!bytes.HasPrefix(body, []byte(`{"notes":[{"body":"nnn`)) {
		panic("the notes list")
	}
	compare("(c) notes list of 20", 500,
		func() { sink = must(jsonformat.Write(notesToks())) },
		func() { sink = must(jsonformat.WriteArray(notesStrToks())) })

	command := kernel.CommandApply{Op: kernel.OpMul(), Arg: 7}
	bodies := []struct{ label, text string }{
		{"(d) request body", `{"cmd":"apply","op":"mul","arg":7}`},
		{"    with spaces", `{"cmd": "apply", "op": "mul", "arg": 7}`},
	}
	for _, body := range bodies {
		request := []byte(body.text)
		if decodeByHand(request) != kernel.Command(command) ||
			must(wire.Request(1, 42, 1, 0, leangage.BodyOf(request))).Cmd != kernel.Command(command) {
			panic("the request body")
		}
		compareAs(body.label, "by hand", "generated", 100_000,
			func() { sink = decodeByHand(request) },
			func() { sink = must(wire.Request(1, 42, 1, 0, leangage.BodyOf(request))) })
		var parse []float64
		for range rounds {
			parse = append(parse, perOp(100_000, func() { sink = leangage.BodyOf(request) }))
		}
		fmt.Printf("    tokens only             %s\n", show(parse))
	}
	accepted := leanfran.Except[kernel.Error, kernel.Reply]{Ok: reply}
	if string(wire.Respond(accepted).Body) != `{"value":6}` {
		panic("the answer")
	}
	compareAs("(e) answer", "by hand", "generated", 100_000,
		func() { sink = httpformat.Response{Status: 200, Body: kernel.EncodeReplyArray(reply)} },
		func() { sink = wire.Respond(accepted) })
}
