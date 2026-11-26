package leangage

import (
	"bytes"
	"encoding/json/jsontext"
	"io"
	"strconv"
	"strings"
	"sync"
	"unicode/utf8"
)

// reading is a decoder of encoding/json's tokens, the reader it reads a body from and the
// buffers the tokens are packed in, kept between requests.
type reading struct {
	body    bytes.Reader
	decoder *jsontext.Decoder
	kinds   []byte
	texts   []byte
	text    []byte
	objects []bool
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

// Tokens are the tokens of the JSON text in body as encoding/json reads them, packed in the
// order of the document into one text: one character for the kind of each token, a line feed,
// and the texts of the numbers, the strings and the keys, each but the last after the count of
// its characters and a colon; a number is the text of its token, a member twice two members. It
// reports false for bytes that are not UTF-8, that encoding/json refuses, or that go on after
// the first value. The generated functions decide everything about the tokens.
func Tokens(body []byte) (string, bool) {
	if !utf8.Valid(body) {
		return "", false
	}
	r := readings.Get().(*reading)
	defer readings.Put(r)
	r.body.Reset(body)
	r.decoder.Reset(&r.body, members, escapes)
	kinds := r.kinds[:0]
	texts := r.texts[:0]
	objects := r.objects[:0]
	defer func() { r.kinds, r.texts, r.objects = kinds, texts, objects }()
	prefix, last := 0, 0
	key := false
	for {
		kind := r.decoder.PeekKind()
		if kind == '"' || kind == '0' {
			if len(kinds) > 0 && len(objects) == 0 {
				return "", false
			}
			value, err := r.decoder.ReadValue()
			if err != nil {
				return "", false
			}
			text := r.text[:0]
			name := kind == '"' && key
			switch {
			case kind == '0':
				text = append(text, value...)
				kinds = append(kinds, '#')
			case name:
				text, _ = jsontext.AppendUnquote(text, value)
				kinds = append(kinds, 'k')
			default:
				text, _ = jsontext.AppendUnquote(text, value)
				kinds = append(kinds, 's')
			}
			r.text = text
			prefix = len(texts)
			texts = strconv.AppendInt(texts, int64(utf8.RuneCount(text)), 10)
			texts = append(texts, ':')
			last = len(texts)
			texts = append(texts, text...)
			key = !name && len(objects) > 0 && objects[len(objects)-1]
			continue
		}
		token, err := r.decoder.ReadToken()
		if err == io.EOF {
			if len(kinds) == 0 || len(objects) != 0 {
				return "", false
			}
			var packed strings.Builder
			packed.Grow(len(kinds) + 1 + len(texts))
			packed.Write(kinds)
			packed.WriteByte('\n')
			packed.Write(texts[:prefix])
			packed.Write(texts[last:])
			return packed.String(), true
		}
		if err != nil || len(kinds) > 0 && len(objects) == 0 {
			return "", false
		}
		switch kind := token.Kind(); kind {
		case '{', '[':
			kinds = append(kinds, byte(kind))
			objects = append(objects, kind == '{')
		case '}', ']':
			kinds = append(kinds, byte(kind))
			objects = objects[:len(objects)-1]
		default:
			kinds = append(kinds, byte(kind))
		}
		key = len(objects) > 0 && objects[len(objects)-1]
	}
}
