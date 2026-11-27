package leangage

import (
	"encoding/hex"
	"fmt"
	"strconv"
	"strings"
	"testing"

	"github.com/conao3/lean-leangage/go/leangage/gen/jsonlexemes"
)

func showLibraryTokens(t *testing.T, body []byte) string {
	t.Helper()
	tokens, ok := Tokens(body)
	if !ok {
		return "none"
	}
	lexemes, err := unpacked(tokens)
	if err != nil {
		t.Fatal(err)
	}
	var words []string
	for _, lexeme := range lexemes {
		switch lexeme := lexeme.(type) {
		case jsonlexemes.LexemeNull:
			words = append(words, "n")
		case jsonlexemes.LexemeBool:
			words = append(words, map[bool]string{true: "t", false: "f"}[lexeme.B])
		case jsonlexemes.LexemeNumber:
			n, err := jsonlexemes.NumberOf(lexeme.Text)
			if err != nil {
				t.Fatal(err)
			}
			if n == nil {
				words = append(words, "#")
			} else {
				words = append(words, "u"+strconv.FormatUint(*n, 10))
			}
		case jsonlexemes.LexemeStr:
			words = append(words, "sx"+hex.EncodeToString([]byte(lexeme.S)))
		case jsonlexemes.LexemeKey:
			words = append(words, "kx"+hex.EncodeToString([]byte(lexeme.S)))
		case jsonlexemes.LexemeArrOpen:
			words = append(words, "[")
		case jsonlexemes.LexemeArrClose:
			words = append(words, "]")
		case jsonlexemes.LexemeObjOpen:
			words = append(words, "{")
		case jsonlexemes.LexemeObjClose:
			words = append(words, "}")
		default:
			t.Fatalf("bad token %#v", lexeme)
		}
	}
	return strings.Join(words, " ")
}

func nested(depth int) (string, string) {
	return strings.Repeat("[", depth) + strings.Repeat("]", depth),
		strings.TrimSuffix(strings.Repeat("[ ", depth)+strings.Repeat("] ", depth), " ")
}

// What encoding/json and Tokens do with the texts on which the JSON libraries of the servers'
// languages differ, and with those at the edges of the grammar. The tokens are written as in
// `lean/RequestOracle.lean`, and `none` is a refused body. encoding/json reads the escape of a
// surrogate outside a pair as U+FFFD, and refuses arrays nested deeper than 10,000.
func TestEncodingJsonOnEdgeCases(t *testing.T) {
	deep200, items200 := nested(200)
	deep2000, items2000 := nested(2000)
	deep10000, items10000 := nested(10000)
	deep10001, _ := nested(10001)
	cases := []struct{ name, body, want string }{
		{"lone high surrogate", `"\ud800"`, "sxefbfbd"},
		{"lone low surrogate", `"\udc00"`, "sxefbfbd"},
		{"surrogate pair", `"😀"`, "sxf09f9880"},
		{"depth 200", deep200, items200},
		{"depth 2000", deep2000, items2000},
		{"depth 10000", deep10000, items10000},
		{"depth 10001", deep10001, "none"},
		{"NaN", `NaN`, "none"},
		{"Infinity", `Infinity`, "none"},
		{"-Infinity", `-Infinity`, "none"},
		{"1e400", `1e400`, "#"},
		{"-0", `-0`, "#"},
		{"1.0", `1.0`, "#"},
		{"1e2", `1e2`, "#"},
		{"2^64-1", `18446744073709551615`, "u18446744073709551615"},
		{"2^64", `18446744073709551616`, "#"},
		{"leading zero", `01`, "none"},
		{"two objects", `{} {}`, "none"},
		{"two numbers", `1 2`, "none"},
		{"one more close", `[]]`, "none"},
		{"member twice", `{"a":1,"a":2}`, "{ kx61 u1 kx61 u2 }"},
		{"upper-case key", `{"CMD":"get"}`, "{ kx434d44 sx676574 }"},
		{"byte order mark", "\xef\xbb\xbf{}", "none"},
		{"UTF-16", "{\x00}\x00", "none"},
		{"byte that is not UTF-8 in a string", "\"\xff\"", "none"},
		{"control character in a string", "\"\x01\"", "none"},
		{"empty", ``, "none"},
		{"spaces only", " \n", "none"},
	}
	for _, c := range cases {
		if got := showLibraryTokens(t, []byte(c.body)); got != c.want {
			if len(got) > 80 {
				got = fmt.Sprintf("%s… (%d bytes)", got[:80], len(got))
			}
			t.Errorf("%s: got %s", c.name, got)
		}
	}
}

// unpacked is the tokens of a packed text, one by one.
func unpacked(packed string) ([]jsonlexemes.Lexeme, error) {
	lexemes, err := jsonlexemes.Unpack(packed)
	if err != nil || lexemes == nil {
		return nil, err
	}
	return *lexemes, nil
}
