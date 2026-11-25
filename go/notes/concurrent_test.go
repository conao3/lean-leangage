package notes

import (
	"bytes"
	"os"
	"os/exec"
	"runtime"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leanharbor/go/notes/kernel"
)

// collect runs a garbage collection until the finalizers that count the leaked values have run.
func collect() {
	for range 10 {
		runtime.GC()
		time.Sleep(5 * time.Millisecond)
	}
}

// The shared command list, run once per copy on tenants of its own with a goroutine per tenant,
// gives every command the reply Lean gives it in order. After Close, no value has leaked.
func TestConcurrentTenantsAgreeWithLean(t *testing.T) {
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
	want := strings.Split(strings.TrimSuffix(string(theirs), "\n"), "\n")
	if len(want) != len(lines) {
		t.Fatalf("the oracle printed %d lines for %d commands", len(want), len(lines))
	}
	leanfran.TrackLeakedValues(true)
	t.Cleanup(func() { leanfran.TrackLeakedValues(false) })
	before := leanfran.LeakedValues()
	_ = kernel.Handle.Init()
	for deadline := time.Now().Add(10 * time.Second); leanfran.LeakedValues() == before; {
		if time.Now().After(deadline) {
			t.Fatal("a value dropped without Close is not counted")
		}
		runtime.GC()
		time.Sleep(5 * time.Millisecond)
	}
	start := leanfran.LeakedValues()
	type step struct {
		actor kernel.Principal
		cmd   kernel.Command
		want  string
	}
	steps := map[uint64][]step{}
	for i, line := range lines {
		actor, cmd := parse(t, line)
		for k := range uint64(8) {
			moved := kernel.Principal{Org: actor.Org + 100*k, User: actor.User}
			steps[moved.Org] = append(steps[moved.Org], step{moved, cmd, want[i]})
		}
	}
	engine := NewEngine()
	var group sync.WaitGroup
	for _, own := range steps {
		group.Go(func() {
			for _, s := range own {
				reply, refusal, err := engine.Execute(s.actor, s.cmd, nil)
				if err != nil {
					t.Error(err)
					return
				}
				got := ""
				if refusal != nil {
					got = "error " + RefusalName(*refusal)
				} else {
					got = "ok " + show(t, reply)
				}
				if got != s.want {
					t.Errorf("%v %#v: got %.120s, want %.120s", s.actor, s.cmd, got, s.want)
					return
				}
			}
		})
	}
	group.Wait()
	engine.Close()
	collect()
	if n := leanfran.LeakedValues() - start; n != 0 {
		t.Fatalf("%d values leaked", n)
	}
}
