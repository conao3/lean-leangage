package leangage

import (
	"bytes"
	"encoding/json"
	"io"
	"unicode/utf8"

	"github.com/conao3/lean-leangage/go/leangage/jsonlexemes"
)

// Tokens are the tokens of the JSON text in body as encoding/json reads them, in the order of
// the document: one character for the kind of each token, and the texts of the numbers, the
// strings and the keys, a number as the text of its token, a member twice as two members. It
// reports false for bytes that are not UTF-8, that encoding/json refuses, or that go on after
// the first value. The generated functions decide everything about the tokens.
func Tokens(body []byte) (jsonlexemes.Tokens, bool) {
	if !utf8.Valid(body) {
		return jsonlexemes.Tokens{}, false
	}
	decoder := json.NewDecoder(bytes.NewReader(body))
	decoder.UseNumber()
	kinds := make([]byte, 0, 16)
	texts := make([]string, 0, 8)
	objects := make([]bool, 0, 4)
	key := false
	for {
		token, err := decoder.Token()
		if err == io.EOF {
			return jsonlexemes.Tokens{Kinds: string(kinds), Texts: texts}, len(kinds) > 0 && len(objects) == 0
		}
		if err != nil || len(kinds) > 0 && len(objects) == 0 {
			return jsonlexemes.Tokens{}, false
		}
		switch token := token.(type) {
		case json.Delim:
			kinds = append(kinds, byte(token))
			if token == '{' || token == '[' {
				objects = append(objects, token == '{')
			} else {
				objects = objects[:len(objects)-1]
			}
			key = len(objects) > 0 && objects[len(objects)-1]
			continue
		case string:
			texts = append(texts, token)
			if key {
				kinds = append(kinds, 'k')
				key = false
				continue
			}
			kinds = append(kinds, 's')
		case json.Number:
			kinds = append(kinds, '#')
			texts = append(texts, string(token))
		case bool:
			if token {
				kinds = append(kinds, 't')
			} else {
				kinds = append(kinds, 'f')
			}
		case nil:
			kinds = append(kinds, 'n')
		}
		key = len(objects) > 0 && objects[len(objects)-1]
	}
}
