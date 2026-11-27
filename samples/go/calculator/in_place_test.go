package calculator

import (
	"sync"
	"testing"

	"github.com/conao3/lean-leangage/samples/go/calculator/gen/kernel"
)

// Commands from several goroutines, some of them refused, leave every user's number as the
// user's own commands set it, and leave the tenant's snapshot with one reference, so Lean
// updates it in place.
func TestSnapshotStaysExclusive(t *testing.T) {
	engine := NewEngine()
	defer engine.Close()
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
					cmd = kernel.CommandApply{Op: kernel.OpAdd(), Arg: arg}
				case 2:
					cmd = kernel.CommandApply{Op: kernel.OpDiv(), Arg: 0}
				default:
					cmd = kernel.CommandGet{}
				}
				reply, refusal, err := engine.Execute(actor, cmd, nil)
				refused := refusal != nil && *refusal == kernel.ErrorDivByZero()
				if err != nil || refused != (arg%4 == 2) {
					t.Errorf("user %d, command %d: %v, %v, %v", user, arg, reply, refusal, err)
					return
				}
				if want := arg/4*8 + 1; arg%4 == 3 && reply.V != want {
					t.Errorf("user %d, command %d: got %v, want %d", user, arg, reply, want)
					return
				}
			}
		})
	}
	group.Wait()
	exclusive := false
	if !engine.Inspect(1, func(snap Snapshot) { exclusive = snap.IsExclusive() }) || !exclusive {
		t.Fatal("the snapshot is shared")
	}
}
