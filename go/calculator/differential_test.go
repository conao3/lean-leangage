package calculator

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"

	"github.com/conao3/lean-leanharbor/go/calculator/kernel"
)

const commandList = "../../testdata/calculator-commands.txt"

func parse(t *testing.T, line string) (kernel.Principal, kernel.Command) {
	words := strings.Split(line, " ")
	number := func(s string) uint64 {
		n, err := strconv.ParseUint(s, 10, 64)
		if err != nil {
			t.Fatalf("bad line %s", line)
		}
		return n
	}
	actor := kernel.Principal{Org: number(words[0]), User: number(words[1])}
	switch {
	case len(words) == 4 && words[2] == "set":
		return actor, kernel.CommandSet{Value: number(words[3])}
	case len(words) == 5 && words[2] == "apply":
		if op, ok := OpNamed(words[3]); ok {
			return actor, kernel.CommandApply{Op: op, Arg: number(words[4])}
		}
	case len(words) == 3 && words[2] == "get":
		return actor, kernel.CommandGet{}
	}
	t.Fatalf("bad line %s", line)
	return actor, nil
}

// The generated Go behind the memory engine against the kernel run natively by Lean
// (`calculator-oracle`), on the shared command list.
func TestGeneratedGoAgreesWithLean(t *testing.T) {
	path, ok := os.LookupEnv("LEANHARBOR_CALCULATOR_ORACLE")
	if !ok {
		t.Fatal("LEANHARBOR_CALCULATOR_ORACLE is required")
	}
	text, err := os.ReadFile(commandList)
	if err != nil {
		t.Fatal(err)
	}
	oracle := exec.Command(path)
	oracle.Stdin = bytes.NewReader(text)
	theirs, err := oracle.Output()
	if err != nil {
		t.Fatal(err)
	}
	lines := strings.Split(strings.TrimSuffix(string(text), "\n"), "\n")
	if len(lines) != 5000 {
		t.Fatalf("%d commands", len(lines))
	}
	want := strings.Split(strings.TrimSuffix(string(theirs), "\n"), "\n")
	if len(want) != len(lines) {
		t.Fatalf("the oracle printed %d lines", len(want))
	}
	engine := NewEngine()
	for i, line := range lines {
		actor, cmd := parse(t, line)
		reply, refusal, err := engine.Execute(actor, cmd, nil)
		if err != nil {
			t.Fatal(err)
		}
		ours := ""
		if refusal != nil {
			ours = "error " + string(kernel.ErrorName(*refusal))
		} else {
			ours = fmt.Sprintf("ok %d", reply.V)
		}
		if ours != want[i] {
			t.Fatalf("line %d: %s: got %s, want %s", i+1, line, ours, want[i])
		}
	}
}
