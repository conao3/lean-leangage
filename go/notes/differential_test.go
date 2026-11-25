package notes

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"testing"

	"github.com/conao3/lean-leanharbor/go/notes/kernel"
)

const commandList = "../../testdata/notes-commands.txt"

func parse(t *testing.T, line string) (kernel.Principal, kernel.Command) {
	words := strings.Split(line, " ")
	number := func(s string) uint64 {
		n, err := strconv.ParseUint(s, 10, 64)
		if err != nil {
			t.Fatalf("bad line %s", line)
		}
		return n
	}
	flag := func(s string) bool {
		if s != "0" && s != "1" {
			t.Fatalf("bad line %s", line)
		}
		return s == "1"
	}
	actor := kernel.Principal{Org: number(words[0]), User: number(words[1])}
	switch {
	case len(words) == 5 && words[2] == "add-member":
		return actor, kernel.CommandAddMember{User: number(words[3]), Admin: flag(words[4])}
	case len(words) == 4 && words[2] == "remove-member":
		return actor, kernel.CommandRemoveMember{User: number(words[3])}
	case len(words) == 6 && words[2] == "put-note":
		return actor, kernel.CommandPutNote{Id: number(words[3]), Body: words[5], Shared: flag(words[4])}
	case len(words) == 4 && words[2] == "delete-note":
		return actor, kernel.CommandDeleteNote{Id: number(words[3])}
	case len(words) == 4 && words[2] == "read-note":
		return actor, kernel.CommandReadNote{Id: number(words[3])}
	case len(words) == 3 && words[2] == "list-notes":
		return actor, kernel.CommandListNotes{}
	case len(words) == 3 && words[2] == "list-members":
		return actor, kernel.CommandListMembers{}
	}
	t.Fatalf("bad line %s", line)
	return actor, nil
}

func bit(b bool) string {
	if b {
		return "1"
	}
	return "0"
}

func note(n kernel.Note) string {
	return fmt.Sprintf("%d:%d:%s:%s", n.Id, n.Owner, bit(n.Shared), n.Body)
}

func show(t *testing.T, reply kernel.Reply) string {
	switch r := reply.(type) {
	case kernel.ReplyDone:
		return "done"
	case kernel.ReplyFound:
		return "found " + note(r.N)
	case kernel.ReplyNotes:
		words := []string{fmt.Sprintf("notes %d", len(r.Ns))}
		for _, n := range r.Ns {
			words = append(words, note(n))
		}
		return strings.Join(words, " ")
	case kernel.ReplyMembers:
		words := []string{fmt.Sprintf("members %d", len(r.Ms))}
		for _, m := range r.Ms {
			words = append(words, fmt.Sprintf("%d:%s", m.User, bit(m.Admin)))
		}
		return strings.Join(words, " ")
	}
	t.Fatalf("unknown reply %v", reply)
	return ""
}

// The generated Go of the notes behind the memory engine against the kernel run natively by
// Lean (`notes-oracle`), on the shared command list.
func TestGeneratedGoAgreesWithLean(t *testing.T) {
	path, ok := os.LookupEnv("LEANHARBOR_NOTES_ORACLE")
	if !ok {
		t.Fatal("LEANHARBOR_NOTES_ORACLE is required")
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
	if len(lines) != 3000 {
		t.Fatalf("%d commands", len(lines))
	}
	want := strings.Split(strings.TrimSuffix(string(theirs), "\n"), "\n")
	if len(want) != len(lines) {
		t.Fatalf("the oracle printed %d lines", len(want))
	}
	engine := NewEngine()
	defer engine.Close()
	for i, line := range lines {
		actor, cmd := parse(t, line)
		reply, refusal, err := engine.Execute(actor, cmd, nil)
		if err != nil {
			t.Fatal(err)
		}
		ours := ""
		if refusal != nil {
			ours = "error " + RefusalName(*refusal)
		} else {
			ours = "ok " + show(t, reply)
		}
		if ours != want[i] {
			t.Fatalf("line %d: %.80s: got %.120s, want %.120s", i+1, line, ours, want[i])
		}
	}
}
