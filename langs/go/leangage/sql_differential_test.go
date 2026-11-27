package leangage_test

import (
	"bytes"
	"encoding/hex"
	"fmt"
	"math/big"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"

	"github.com/conao3/lean-leangage/langs/go/leangage/gen/sql"
	"github.com/conao3/leanfran-go"
)

// The line format is described in `langs/lean/SqlOracle.lean`.
const statementList = "../../../testdata/sql-statements.txt"

type sqlRunner struct {
	t      *testing.T
	line   string
	schema []sql.Tab
}

func (r *sqlRunner) unhex(s string) []byte {
	b, err := hex.DecodeString(s)
	if err != nil {
		r.t.Fatalf("bad hex in %s", r.line)
	}
	return b
}

func (r *sqlRunner) nat(s string) *big.Int {
	n, ok := new(big.Int).SetString(s, 10)
	if !ok {
		r.t.Fatalf("bad number in %s", r.line)
	}
	return n
}

func (r *sqlRunner) int64(s string) int64 {
	n, err := strconv.ParseInt(s, 10, 64)
	if err != nil {
		r.t.Fatalf("bad int64 in %s", r.line)
	}
	return n
}

func (r *sqlRunner) value(s string) sql.Val {
	switch tag, v := s[:1], s[1:]; {
	case tag == "i":
		return sql.ValInt{V: r.int64(v)}
	case s == "b0":
		return sql.ValBool{V: false}
	case s == "b1":
		return sql.ValBool{V: true}
	case tag == "t":
		return sql.ValText{V: string(r.unhex(v))}
	case tag == "y":
		return sql.ValBytes{V: r.unhex(v)}
	case s == "n":
		return sql.ValNull{}
	}
	r.t.Fatalf("bad value %s", s)
	return nil
}

func (r *sqlRunner) values(ws []string) []sql.Val {
	vs := []sql.Val{}
	for _, w := range ws {
		vs = append(vs, r.value(w))
	}
	return vs
}

func showValue(v sql.Val) string {
	switch v := v.(type) {
	case sql.ValInt:
		return fmt.Sprintf("i%d", v.V)
	case sql.ValBool:
		if v.V {
			return "b1"
		}
		return "b0"
	case sql.ValText:
		return "t" + hex.EncodeToString([]byte(v.V))
	case sql.ValBytes:
		return "y" + hex.EncodeToString(v.V)
	default:
		return "n"
	}
}

func (r *sqlRunner) column(s string) sql.Col {
	parts := strings.Split(s, ":")
	kinds := map[string]sql.Kind{
		"int": sql.KindInt(), "bool": sql.KindBool(), "text": sql.KindText(), "bytes": sql.KindBytes(),
	}
	kind, ok := kinds[parts[1]]
	if !ok {
		r.t.Fatalf("bad kind in %s", r.line)
	}
	return sql.Col{Name: string(r.unhex(parts[0])), Kind: kind, Nullable: parts[2] == "1"}
}

func (r *sqlRunner) render(q sql.Sql) string {
	text, err := sql.Render(q)
	if err != nil {
		r.t.Fatal(err)
	}
	return hex.EncodeToString([]byte(text))
}

func (r *sqlRunner) show(compiled *leanfran.Pair[sql.Sql, []sql.Val], err error) string {
	if err != nil {
		r.t.Fatal(err)
	}
	if compiled == nil {
		return "none"
	}
	words := []string{"sql", r.render(compiled.Fst)}
	for _, v := range compiled.Snd {
		words = append(words, showValue(v))
	}
	return strings.Join(words, " ")
}

func (r *sqlRunner) compile(tenant string, w sql.Write) string {
	s, err := sql.Plan(w)
	if err != nil {
		r.t.Fatal(err)
	}
	return r.show(sql.Compile(r.schema, r.int64(tenant), s))
}

func (r *sqlRunner) run(line string) string {
	r.line = line
	words := strings.Split(line, " ")
	switch {
	case len(words) == 1 && words[0] == "reset":
		r.schema = nil
		return "ok"
	case len(words) >= 3 && words[0] == "table":
		cols := []sql.Col{}
		for _, c := range words[3:] {
			cols = append(cols, r.column(c))
		}
		r.schema = append(r.schema, sql.Tab{Name: string(r.unhex(words[1])), Cols: cols, Kl: r.nat(words[2])})
		valid, err := sql.Valid(r.schema)
		if err != nil {
			r.t.Fatal(err)
		}
		return fmt.Sprintf("valid %t", valid)
	case len(words) == 1 && words[0] == "create":
		out := []string{"create"}
		for _, tab := range r.schema {
			q, err := sql.Create(tab)
			if err != nil {
				r.t.Fatal(err)
			}
			out = append(out, r.render(q))
		}
		return strings.Join(out, " ")
	case len(words) >= 4 && words[0] == "put":
		return r.compile(words[1], sql.WritePut{Table: r.nat(words[2]), KeyLen: r.nat(words[3]), Row: r.values(words[4:])})
	case len(words) >= 3 && words[0] == "del":
		return r.compile(words[1], sql.WriteDel{Table: r.nat(words[2]), Key: r.values(words[3:])})
	case len(words) == 5 && words[0] == "delwhere":
		return r.compile(words[1], sql.WriteDelWhere{Table: r.nat(words[2]), Col: r.nat(words[3]), Val: r.value(words[4])})
	case len(words) == 3 && words[0] == "select":
		return r.show(sql.Select(r.schema, r.int64(words[1]), r.nat(words[2]), nil))
	case len(words) == 5 && words[0] == "select":
		filter := &leanfran.Pair[*big.Int, sql.Val]{Fst: r.nat(words[3]), Snd: r.value(words[4])}
		return r.show(sql.Select(r.schema, r.int64(words[1]), r.nat(words[2]), filter))
	}
	r.t.Fatalf("bad line %s", line)
	return ""
}

// The generated Go SQL compiler against the one run natively by Lean (`sql-oracle`), on the
// shared statement list.
func TestGeneratedGoSqlAgreesWithLean(t *testing.T) {
	path, ok := os.LookupEnv("LEANGAGE_SQL_ORACLE")
	if !ok {
		t.Fatal("LEANGAGE_SQL_ORACLE is required")
	}
	text, err := os.ReadFile(statementList)
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(path)
	cmd.Stdin = bytes.NewReader(text)
	theirs, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	r := &sqlRunner{t: t}
	lines := strings.Split(strings.TrimSuffix(string(text), "\n"), "\n")
	theirLines := strings.Split(strings.TrimSuffix(string(theirs), "\n"), "\n")
	if len(lines) != len(theirLines) {
		t.Fatalf("%d lines, the oracle printed %d", len(lines), len(theirLines))
	}
	compiled := 0
	for i, line := range lines {
		ours := r.run(line)
		if strings.HasPrefix(ours, "sql ") {
			compiled++
		}
		if ours != theirLines[i] {
			t.Fatalf("line %d: %s\nours:   %s\ntheirs: %s", i+1, line, ours, theirLines[i])
		}
	}
	if compiled <= 100 {
		t.Fatalf("only %d statements compiled", compiled)
	}
}
