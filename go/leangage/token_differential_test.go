package leangage_test

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/conao3/lean-leangage/go/leangage/gen/token"
)

// The line format is described in `lean/TokenOracle.lean`.
const tokenCases = "../../testdata/token-cases.txt"

func tokenBytes(t *testing.T, s string) []byte {
	b, err := hex.DecodeString(strings.TrimPrefix(s, "x"))
	if err != nil || !strings.HasPrefix(s, "x") {
		t.Fatalf("bad bytes %s", s)
	}
	return b
}

func showBytes(b []byte) string {
	return "x" + hex.EncodeToString(b)
}

func runToken(t *testing.T, line string) string {
	number := func(s string) uint64 {
		n, err := strconv.ParseUint(s, 10, 64)
		if err != nil {
			t.Fatalf("bad number in %s", line)
		}
		return n
	}
	words := strings.Split(line, " ")
	switch {
	case len(words) == 2 && words[0] == "parse":
		raw := tokenBytes(t, words[1])
		out := "none"
		if p := token.Parse(raw); p != nil {
			out = fmt.Sprintf("parsed %d %d %d %s %s", p.Tenant, p.User, p.Exp, showBytes(p.Payload), showBytes(p.Sig))
		}
		fromString := "none"
		p, err := token.ParseString(string(raw))
		if err != nil && utf8.Valid(raw) {
			t.Fatalf("ParseString of %q: %v", raw, err)
		}
		if p != nil {
			fromString = fmt.Sprintf("parsed %d %d %d %s %s", p.Tenant, p.User, p.Exp, showBytes(p.Payload), showBytes(p.Sig))
		}
		if fromString != out {
			t.Fatalf("ParseString of %q: %s, Parse: %s", raw, fromString, out)
		}
		return out
	case len(words) == 5 && words[0] == "issue":
		payload := token.EncodePayload(number(words[1]), number(words[2]), number(words[3]))
		return "token " + showBytes(token.Join(payload, tokenBytes(t, words[4])))
	}
	t.Fatalf("bad line %s", line)
	return ""
}

// The generated Go token functions against the ones run natively by Lean (`token-oracle`), on the
// shared token list. Each token is also split by ParseString, which must give what Parse gives and
// refuses a token that is not UTF-8.
func TestGeneratedGoTokenFunctionsAgreeWithLean(t *testing.T) {
	path, ok := os.LookupEnv("LEANGAGE_TOKEN_ORACLE")
	if !ok {
		t.Fatal("LEANGAGE_TOKEN_ORACLE is required")
	}
	text, err := os.ReadFile(tokenCases)
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(path)
	cmd.Stdin = bytes.NewReader(text)
	theirs, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	lines := strings.Split(strings.TrimSuffix(string(text), "\n"), "\n")
	theirLines := strings.Split(strings.TrimSuffix(string(theirs), "\n"), "\n")
	if len(lines) != len(theirLines) {
		t.Fatalf("%d lines, the oracle printed %d", len(lines), len(theirLines))
	}
	parsed, rejected := 0, 0
	for i, line := range lines {
		ours := runToken(t, line)
		if strings.HasPrefix(ours, "parsed ") {
			parsed++
		}
		if ours == "none" {
			rejected++
		}
		if ours != theirLines[i] {
			t.Fatalf("line %d: %s\nours:   %s\ntheirs: %s", i+1, line, ours, theirLines[i])
		}
	}
	if parsed <= 100 || rejected <= 100 {
		t.Fatalf("%d parsed and %d rejected tokens", parsed, rejected)
	}
}
