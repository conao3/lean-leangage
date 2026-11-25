package pg_test

// Every kind of Val, NULL included, written by the engine and read back unchanged, in a table
// whose name holds `"`, a space and a letter outside ASCII. An empty byte string, nil or not,
// is stored as empty bytes and not as NULL. A text holding NUL, which PostgreSQL cannot store,
// fails the command instead of storing something else.

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"slices"
	"strings"
	"testing"

	"github.com/conao3/lean-leanharbor/go/leanharbor"
	"github.com/conao3/lean-leanharbor/go/leanharbor/pg"
	"github.com/conao3/lean-leanharbor/go/leanharbor/pg/pgtest"
	"github.com/conao3/lean-leanharbor/go/leanharbor/sql"
)

type table = [][]sql.Val

// rowsCmd is a command of storedRows: a row to put, or nil to read the table.
type rowsCmd struct{ put []sql.Val }

type noRefusal struct{}

// storedRows are the rows of one table, stored as the commands give them.
type storedRows struct{}

func (storedRows) Init() table { return table{} }

func (storedRows) Tenant(tenant uint64) uint64 { return tenant }

func (storedRows) Transition(_ uint64, snap table, c rowsCmd) (table, table, *noRefusal) {
	if c.put != nil {
		return table{c.put}, table{}, nil
	}
	return table{}, snap, nil
}

func (storedRows) Apply(snap table, _ table) table { return snap }

func (k storedRows) Scoped(run func(leanharbor.Kernel[uint64, table, rowsCmd, table, table, noRefusal])) {
	run(k)
}

func (storedRows) ReadOnly(c rowsCmd) bool { return c.put == nil }

func (storedRows) Tables() []sql.Tab {
	return []sql.Tab{{
		Name: `odd "näme"`,
		Cols: []sql.Col{
			{Name: "k", Kind: sql.KindInt(), Nullable: false},
			{Name: "b", Kind: sql.KindBool(), Nullable: true},
			{Name: `t "x"`, Kind: sql.KindText(), Nullable: true},
			{Name: "y", Kind: sql.KindBytes(), Nullable: true},
			{Name: "i", Kind: sql.KindInt(), Nullable: true},
		},
		Kl: big.NewInt(1),
	}}
}

func (storedRows) Load(rows [][][]sql.Val) (table, bool) {
	if len(rows) != 1 {
		return nil, false
	}
	return rows[0], true
}

func (storedRows) Writes(ws table) []sql.Write {
	out := []sql.Write{}
	for _, row := range ws {
		out = append(out, sql.WritePut{Table: big.NewInt(0), KeyLen: big.NewInt(1), Row: row})
	}
	return out
}

func (storedRows) EncodeStoredReply(table) []byte { return nil }

func (storedRows) DecodeStoredReply([]byte) (table, bool) { return nil, false }

func int64Val(v int64) sql.Val { return sql.ValInt{V: v} }

// show is a row as text that tells NULL from empty bytes and does not tell a nil slice from an
// empty one.
func show(row []sql.Val) string {
	parts := []string{}
	for _, v := range row {
		switch v := v.(type) {
		case sql.ValInt:
			parts = append(parts, fmt.Sprintf("int %d", v.V))
		case sql.ValBool:
			parts = append(parts, fmt.Sprintf("bool %v", v.V))
		case sql.ValText:
			parts = append(parts, fmt.Sprintf("text %q", v.V))
		case sql.ValBytes:
			parts = append(parts, fmt.Sprintf("bytes %x", v.V))
		case sql.ValNull:
			parts = append(parts, "null")
		default:
			parts = append(parts, fmt.Sprintf("%#v", v))
		}
	}
	return strings.Join(parts, ", ")
}

func shown(rows table) []string {
	out := []string{}
	for _, row := range rows {
		out = append(out, show(row))
	}
	slices.Sort(out)
	return out
}

func TestEveryKindReadsBackAsWritten(t *testing.T) {
	t.Parallel()
	url := pgtest.Start(t).Locked(t, storedRows{}.Tables(), "values_kinds")
	e, err := pg.Connect(storedRows{}, url, 2, pg.DefaultConfig())
	if err != nil {
		t.Fatalf("the engine connects: %v", err)
	}
	defer e.Close()
	allBytes := make([]byte, 256)
	for i := range allBytes {
		allBytes[i] = byte(i)
	}
	rows := table{
		{int64Val(math.MinInt64), sql.ValBool{V: true}, sql.ValText{V: ""}, sql.ValBytes{V: nil}, int64Val(math.MaxInt64)},
		{int64Val(-1), sql.ValBool{V: false}, sql.ValText{V: "\"quoted\" 'single' \\ é 日本 🦀 \x7f"},
			sql.ValBytes{V: allBytes}, int64Val(0)},
		{int64Val(0), sql.ValNull{}, sql.ValNull{}, sql.ValNull{}, sql.ValNull{}},
		{int64Val(math.MaxInt64), sql.ValBool{V: true}, sql.ValText{V: strings.Repeat("x", 10_000)},
			sql.ValBytes{V: []byte{0}}, sql.ValNull{}},
		{int64Val(1), sql.ValNull{}, sql.ValNull{}, sql.ValBytes{V: []byte{}}, sql.ValNull{}},
	}
	for _, row := range rows {
		got, refusal, err := e.Execute(1, rowsCmd{put: row}, nil)
		if err != nil || refusal != nil || len(got) != 0 {
			t.Fatalf("%s: %v %v %v", show(row), got, refusal, err)
		}
	}
	replaced := []sql.Val{int64Val(-1), sql.ValNull{}, sql.ValText{V: "new"}, sql.ValNull{}, int64Val(7)}
	if _, _, err := e.Execute(1, rowsCmd{put: replaced}, nil); err != nil {
		t.Fatal(err)
	}
	expected := slices.Clone(rows)
	expected[1] = replaced
	read, _, err := e.Execute(1, rowsCmd{}, nil)
	if err != nil {
		t.Fatal(err)
	}
	if got, want := shown(read), shown(expected); !slices.Equal(got, want) {
		t.Fatalf("read back:\n%s\nwant:\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
	if other, _, err := e.Execute(2, rowsCmd{}, nil); err != nil || len(other) != 0 {
		t.Fatalf("another tenant: %v %v", other, err)
	}

	nul := []sql.Val{int64Val(5), sql.ValNull{}, sql.ValText{V: "a\x00b"}, sql.ValNull{}, sql.ValNull{}}
	if _, _, err := e.Execute(1, rowsCmd{put: nul}, nil); !errors.Is(err, leanharbor.ErrDatabase) {
		t.Fatalf("a text holding NUL: %v", err)
	}
	read, _, err = e.Execute(1, rowsCmd{}, nil)
	if err != nil || len(read) != len(rows) {
		t.Fatalf("nothing stored: %d rows, %v", len(read), err)
	}
}
