package calculator

import (
	"runtime"
	"sync"
	"testing"
	"time"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/samples/go/calculator/gen/kernel"
)

// copies is how many times the concurrent tests run the shared command list, each time on
// other tenants.
const copies = 8

// collect runs a garbage collection until the finalizers that count the leaked values have run.
func collect() {
	for range 10 {
		runtime.GC()
		time.Sleep(5 * time.Millisecond)
	}
}

// trackLeaks counts the values that are collected while they hold a Lean reference, from now to
// the end of the test, and checks that counting sees a value dropped without Close.
func trackLeaks(t *testing.T) func() int64 {
	t.Helper()
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
	return func() int64 {
		collect()
		return leanfran.LeakedValues() - start
	}
}

// The shared command list, run once per copy on tenants of its own with a goroutine per user,
// gives every command the reply Lean gives it in order: each user's number is the user's own,
// so the commands of one goroutine see only its own. After Close, no value has leaked.
func TestConcurrentTenantsAgreeWithLean(t *testing.T) {
	lines, want := commands(t)
	leaked := trackLeaks(t)
	type user struct{ org, user uint64 }
	type step struct {
		actor kernel.Principal
		cmd   kernel.Command
		want  string
	}
	steps := map[user][]step{}
	for i, line := range lines {
		actor, cmd := parse(t, line)
		for k := range uint64(copies) {
			moved := kernel.Principal{Org: actor.Org + 100*k, User: actor.User}
			at := user{moved.Org, moved.User}
			steps[at] = append(steps[at], step{moved, cmd, want[i]})
		}
	}
	engine := NewEngine()
	var group sync.WaitGroup
	for _, own := range steps {
		group.Go(func() {
			for _, s := range own {
				if got := answer(engine.Execute(s.actor, s.cmd, nil)); got != s.want {
					t.Errorf("%v %#v: got %s, want %s", s.actor, s.cmd, got, s.want)
					return
				}
			}
		})
	}
	group.Wait()
	engine.Close()
	if n := leaked(); n != 0 {
		t.Fatalf("%d values leaked", n)
	}
}
