package leangage

import (
	"bytes"
	"encoding/json"
	"io"
	"unicode/utf8"

	"github.com/conao3/lean-leangage/go/leangage/jsonlexemes"
)

// Lexemes are the tokens of the JSON text in body as encoding/json reads them, in the order of
// the document: a number as the text of its token, a member twice as two members. It reports
// false for bytes that are not UTF-8, that encoding/json refuses, or that go on after the first
// value. The generated functions decide everything about the tokens.
func Lexemes(body []byte) ([]jsonlexemes.Lexeme, bool) {
	if !utf8.Valid(body) {
		return nil, false
	}
	decoder := json.NewDecoder(bytes.NewReader(body))
	decoder.UseNumber()
	out := make([]jsonlexemes.Lexeme, 0, 16)
	objects := make([]bool, 0, 4)
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
				out = append(out, jsonlexemes.LexemeObjOpen{})
				objects = append(objects, true)
			case '[':
				out = append(out, jsonlexemes.LexemeArrOpen{})
				objects = append(objects, false)
			case '}':
				out = append(out, jsonlexemes.LexemeObjClose{})
				objects = objects[:len(objects)-1]
			case ']':
				out = append(out, jsonlexemes.LexemeArrClose{})
				objects = objects[:len(objects)-1]
			}
			key = len(objects) > 0 && objects[len(objects)-1]
			continue
		case string:
			if key {
				out = append(out, jsonlexemes.LexemeKey{S: token})
				key = false
				continue
			}
			out = append(out, jsonlexemes.LexemeStr{S: token})
		case json.Number:
			out = append(out, jsonlexemes.LexemeNumber{Text: string(token)})
		case bool:
			out = append(out, jsonlexemes.LexemeBool{B: token})
		case nil:
			out = append(out, jsonlexemes.LexemeNull{})
		}
		key = len(objects) > 0 && objects[len(objects)-1]
	}
}
