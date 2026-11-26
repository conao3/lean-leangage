package leangage

import (
	"bytes"
	"encoding/json/jsontext"
	"io"
	"sync"
	"unicode/utf8"

	"github.com/conao3/lean-leangage/go/leangage/jsonlexemes"
)

// reading is a decoder of encoding/json's tokens and the reader it reads a body from, kept
// between requests.
type reading struct {
	body    bytes.Reader
	decoder *jsontext.Decoder
}

// members keeps a member that comes twice, and escapes keeps the escape of a surrogate outside a
// pair as U+FFFD; Tokens refuses bytes that are not UTF-8 before the decoder sees them.
var (
	members = jsontext.AllowDuplicateNames(true)
	escapes = jsontext.AllowInvalidUTF8(true)
)

var readings = sync.Pool{New: func() any {
	r := new(reading)
	r.decoder = jsontext.NewDecoder(&r.body, members, escapes)
	return r
}}

// Tokens are the tokens of the JSON text in body as encoding/json reads them, in the order of
// the document: one character for the kind of each token, and the texts of the numbers, the
// strings and the keys, a number as the text of its token, a member twice as two members. It
// reports false for bytes that are not UTF-8, that encoding/json refuses, or that go on after
// the first value. The generated functions decide everything about the tokens.
func Tokens(body []byte) (jsonlexemes.Tokens, bool) {
	if !utf8.Valid(body) {
		return jsonlexemes.Tokens{}, false
	}
	r := readings.Get().(*reading)
	defer readings.Put(r)
	r.body.Reset(body)
	r.decoder.Reset(&r.body, members, escapes)
	kinds := make([]byte, 0, 16)
	texts := make([]string, 0, 8)
	objects := make([]bool, 0, 4)
	key := false
	for {
		token, err := r.decoder.ReadToken()
		if err == io.EOF {
			return jsonlexemes.Tokens{Kinds: string(kinds), Texts: texts}, len(kinds) > 0 && len(objects) == 0
		}
		if err != nil || len(kinds) > 0 && len(objects) == 0 {
			return jsonlexemes.Tokens{}, false
		}
		switch kind := token.Kind(); kind {
		case '{', '[':
			kinds = append(kinds, byte(kind))
			objects = append(objects, kind == '{')
		case '}', ']':
			kinds = append(kinds, byte(kind))
			objects = objects[:len(objects)-1]
		case '"':
			texts = append(texts, token.String())
			if key {
				kinds = append(kinds, 'k')
				key = false
				continue
			}
			kinds = append(kinds, 's')
		case '0':
			kinds = append(kinds, '#')
			texts = append(texts, token.String())
		default:
			kinds = append(kinds, byte(kind))
		}
		key = len(objects) > 0 && objects[len(objects)-1]
	}
}
