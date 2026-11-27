// Package notes is the notes: the kernel is `samples/lean/Notes/Kernel.lean`, generated to the
// package kernel. Its Transition is the kernel's `handle` behind the guard of
// `langs/lean/Leangage/Authz.lean`.
package notes

import (
	"errors"
	"fmt"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/langs/go/leangage"
	"github.com/conao3/lean-leangage/samples/go/notes/gen/kernel"
)

// Snapshot is one tenant's state, kept as a Lean value.
type Snapshot = leanfran.Value[kernel.Snapshot]

// WriteSet is the writes of an accepted command, kept as a Lean value.
type WriteSet = leanfran.Value[leanfran.ListType[kernel.Write]]

// Refusal is a refusal of the guarded kernel: the kernel's own, or the guard's.
type Refusal = kernel.LeangageAuthzGuardedNotesKernelError

// Notes implements the kernel contract of the notes.
type Notes struct {
	scope *leanfran.ValueScope
}

// Engine is the memory engine of the notes.
type Engine = leangage.MemoryEngine[kernel.Principal, Snapshot, kernel.Command, WriteSet, kernel.Reply, Refusal]

func NewEngine() *Engine {
	return leangage.NewMemoryEngine(Notes{})
}

func must[T any](value T, err error) T {
	if err != nil {
		panic(err)
	}
	return value
}

func (n Notes) Init() Snapshot {
	return kernel.Handle.In(n.scope).Init()
}

func (Notes) Tenant(actor kernel.Principal) uint64 {
	return kernel.Tenant(actor)
}

func (Notes) Scoped(
	region *leanfran.Region,
	run func(leangage.Kernel[kernel.Principal, Snapshot, kernel.Command, WriteSet, kernel.Reply, Refusal]),
) {
	region.WithValues(func(scope *leanfran.ValueScope) {
		run(Notes{scope})
	})
}

func (n Notes) Transition(
	actor kernel.Principal, snap Snapshot, cmd kernel.Command,
) (WriteSet, kernel.Reply, *Refusal) {
	values, handle := kernel.Value.In(n.scope), kernel.Handle.In(n.scope)
	who := values.NewPrincipal(actor)
	what := must(values.NewCommand(cmd))
	ws, reply, err := handle.Transition(who.Take(), snap.Borrow(), what.Take())
	if refusal, ok := errors.AsType[*leanfran.ExceptError[Refusal]](err); ok {
		return WriteSet{}, nil, &refusal.Value
	}
	if err != nil {
		panic(err)
	}
	defer reply.CloseIn(n.scope)
	return ws, values.ReadReply(reply), nil
}

func (n Notes) Apply(snap Snapshot, ws WriteSet) Snapshot {
	return kernel.Handle.In(n.scope).Apply(snap.Take(), ws.Take())
}

func (n Notes) Release(snap Snapshot) {
	snap.CloseIn(n.scope)
}

// RefusalName is the name of a refusal.
func RefusalName(refusal Refusal) string {
	switch r := refusal.(type) {
	case kernel.LeangageAuthzGuardedNotesKernelErrorDenied:
		return "denied"
	case kernel.LeangageAuthzGuardedNotesKernelErrorApp:
		switch r.E {
		case kernel.ErrorNotFound():
			return "not_found"
		case kernel.ErrorBadText():
			return "bad_text"
		}
	}
	panic(fmt.Sprintf("unknown refusal %v", refusal))
}
