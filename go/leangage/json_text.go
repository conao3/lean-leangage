package leangage

import (
	"bytes"
	"encoding/json"
	"io"
	"unicode/utf8"

	"github.com/conao3/lean-leangage/go/leangage/jsonitems"
)

// Lexemes are the tokens of the JSON text in body as encoding/json reads them, in the order of
// the document: a number as the text of its token, a member twice as two members. It reports
// false for bytes that are not UTF-8, that encoding/json refuses, or that go on after the first
// value. The generated functions decide everything about the tokens.
func Lexemes(body []byte) ([]jsonitems.Lexeme, bool) {
	if !utf8.Valid(body) {
		return nil, false
	}
	decoder := json.NewDecoder(bytes.NewReader(body))
	decoder.UseNumber()
	var out []jsonitems.Lexeme
	var objects []bool
	key := false
	for {
		token, err := decoder.Token()
		if err == io.EOF {
			return out, len(out) > 0 && len(objects) == 0
		}
		if err != nil || len(out) > 0 && len(objects) == 0 {
			return nil, false
		}
		switch token := token.(type) {
		case json.Delim:
			switch token {
			case '{':
				out = append(out, jsonitems.LexemeObjOpen{})
				objects = append(objects, true)
			case '[':
				out = append(out, jsonitems.LexemeArrOpen{})
				objects = append(objects, false)
			case '}':
				out = append(out, jsonitems.LexemeObjClose{})
				objects = objects[:len(objects)-1]
			case ']':
				out = append(out, jsonitems.LexemeArrClose{})
				objects = objects[:len(objects)-1]
			}
			key = len(objects) > 0 && objects[len(objects)-1]
			continue
		case string:
			if key {
				out = append(out, jsonitems.LexemeKey{S: token})
				key = false
				continue
			}
			out = append(out, jsonitems.LexemeStr{S: token})
		case json.Number:
			out = append(out, jsonitems.LexemeNumber{Text: string(token)})
		case bool:
			out = append(out, jsonitems.LexemeBool{B: token})
		case nil:
			out = append(out, jsonitems.LexemeNull{})
		}
		key = len(objects) > 0 && objects[len(objects)-1]
	}
}
