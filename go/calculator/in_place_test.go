package calculator

import (
	"sync"
	"testing"

	"github.com/conao3/lean-leanharbor/go/calculator/kernel"
)

// The engine gives `apply` the only reference to a tenant's snapshot, so Lean rewrites the row
// of the last user of a large tenant without copying the rows before it: a command allocates
// less than `apply` on a borrowed snapshot of the same size, which allocates one new row for
// every row.
func TestSnapshotIsUpdatedInPlace(t *testing.T) {
	const users = 1000
	engine := NewEngine()
	rows := make([]kernel.Memory, users)
	for user := range uint64(users) {
		_, _, _ = engine.Execute(kernel.Principal{Org: 1, User: user}, kernel.CommandSet{Value: 1}, nil)
		rows[user] = kernel.Memory{User: user, Value: 1}
	}
	last := kernel.Principal{Org: 1, User: users - 1}
	inPlace := testing.AllocsPerRun(100, func() {
		_, _, _ = engine.Execute(last, kernel.CommandSet{Value: 2}, nil)
	})
	shared := must(kernel.NewSnapshotValue(kernel.Snapshot{Memories: rows}))
	defer shared.Close()
	copied := testing.AllocsPerRun(100, func() {
		ws := must(kernel.NewOptionMemoryValue(&kernel.Memory{User: users - 1, Value: 2}))
		must(kernel.ApplyValue(shared.Borrow(), ws.Take())).Close()
	})
	if inPlace+users/2 > copied {
		t.Fatalf("%v allocations for one command, %v for a copy of %d rows", inPlace, copied, users)
	}
}

// Commands from several goroutines, some of them refused, leave every user's number as the
// user's own commands set it.
func TestCommandsFromSeveralGoroutines(t *testing.T) {
	engine := NewEngine()
	var group sync.WaitGroup
	for user := range uint64(8) {
		group.Go(func() {
			actor := kernel.Principal{Org: 1, User: user}
			for arg := range uint64(200) {
				var cmd kernel.Command
				switch arg % 4 {
				case 0:
					cmd = kernel.CommandSet{Value: arg}
				case 1:
					cmd = kernel.CommandApply{Op: kernel.OpAdd, Arg: arg}
				case 2:
					cmd = kernel.CommandApply{Op: kernel.OpDiv, Arg: 0}
				default:
					cmd = kernel.CommandGet{}
				}
				reply, refusal, err := engine.Execute(actor, cmd, nil)
				refused := refusal != nil && *refusal == kernel.ErrorDivByZero
				if err != nil || refused != (arg%4 == 2) {
					t.Errorf("user %d, command %d: %v, %v, %v", user, arg, reply, refusal, err)
					return
				}
				if want := arg/4*8 + 1; arg%4 == 3 && reply.(kernel.ReplyValue).V != want {
					t.Errorf("user %d, command %d: got %v, want %d", user, arg, reply, want)
					return
				}
			}
		})
	}
	group.Wait()
}
