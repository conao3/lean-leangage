package leanharbor_test

import (
	"bytes"
	"encoding/hex"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/conao3/lean-leanharbor/go/leanharbor/jsonformat"
)

// The line format is described in `lean/JsonOracle.lean`.
const jsonCases = "../../testdata/json-cases.txt"

func jsonTok(t *testing.T, word string) jsonformat.Tok {
	hexBytes := func(s string) []byte {
		b, err := hex.DecodeString(s)
		if err != nil {
			t.Fatalf("bad bytes %s", word)
		}
		return b
	}
	switch {
	case word == "n":
		return jsonformat.TokNull{}
	case word == "t":
		return jsonformat.TokBool{B: true}
	case word == "f":
		return jsonformat.TokBool{B: false}
	case word == "[":
		return jsonformat.TokArrOpen{}
	case word == "]":
		return jsonformat.TokArrClose{}
	case word == "{":
		return jsonformat.TokObjOpen{}
	case word == "}":
		return jsonformat.TokObjClose{}
	case strings.HasPrefix(word, "u"):
		n, err := strconv.ParseUint(word[1:], 10, 64)
		if err != nil {
			t.Fatalf("bad number %s", word)
		}
		return jsonformat.TokNum{N: n}
	case strings.HasPrefix(word, "sx"):
		return jsonformat.TokStr{S: hexBytes(word[2:])}
	case strings.HasPrefix(word, "kx"):
		return jsonformat.TokKey{S: hexBytes(word[2:])}
	}
	t.Fatalf("bad token %s", word)
	return nil
}

func runJSON(t *testing.T, line string) string {
	words := strings.Split(line, " ")
	if words[0] != "write" {
		t.Fatalf("bad line %s", line)
	}
	toks := make([]jsonformat.Tok, 0, len(words)-1)
	for _, w := range words[1:] {
		toks = append(toks, jsonTok(t, w))
	}
	out, err := jsonformat.Write(toks)
	if err != nil {
		t.Fatal(err)
	}
	if strToks, ok := jsonStrToks(toks); ok {
		fromStrings, err := jsonformat.WriteArray(strToks)
		if err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(fromStrings, out) {
			t.Fatalf("WriteArray of %s: %s", line, showBytes(fromStrings))
		}
	}
	return "json " + showBytes(out)
}

// jsonStrToks are the tokens with strings, if every string is UTF-8.
func jsonStrToks(toks []jsonformat.Tok) ([]jsonformat.StrTok, bool) {
	out := make([]jsonformat.StrTok, 0, len(toks))
	for _, tok := range toks {
		switch tok := tok.(type) {
		case jsonformat.TokNull:
			out = append(out, jsonformat.StrTokNull{})
		case jsonformat.TokBool:
			out = append(out, jsonformat.StrTokBool{B: tok.B})
		case jsonformat.TokNum:
			out = append(out, jsonformat.StrTokNum{N: tok.N})
		case jsonformat.TokStr:
			if !utf8.Valid(tok.S) {
				return nil, false
			}
			out = append(out, jsonformat.StrTokStr{S: string(tok.S)})
		case jsonformat.TokKey:
			if !utf8.Valid(tok.S) {
				return nil, false
			}
			out = append(out, jsonformat.StrTokKey{S: string(tok.S)})
		case jsonformat.TokArrOpen:
			out = append(out, jsonformat.StrTokArrOpen{})
		case jsonformat.TokArrClose:
			out = append(out, jsonformat.StrTokArrClose{})
		case jsonformat.TokObjOpen:
			out = append(out, jsonformat.StrTokObjOpen{})
		case jsonformat.TokObjClose:
			out = append(out, jsonformat.StrTokObjClose{})
		}
	}
	return out, true
}

// The generated Go JSON writer against the one run natively by Lean (`json-oracle`), on the shared
// token lists. A list whose strings are UTF-8 is also written by WriteArray, which must write what
// Write writes.
func TestGeneratedGoJSONWriterAgreesWithLean(t *testing.T) {
	path, ok := os.LookupEnv("LEANHARBOR_JSON_ORACLE")
	if !ok {
		t.Fatal("LEANHARBOR_JSON_ORACLE is required")
	}
	text, err := os.ReadFile(jsonCases)
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
	for i, line := range lines {
		if ours := runJSON(t, line); ours != theirLines[i] {
			t.Fatalf("line %d: %s\nours:   %s\ntheirs: %s", i+1, line, ours, theirLines[i])
		}
	}
}
