// Package calculator is the calculator: the kernel is `lean/Calculator/Kernel.lean`, its table
// `lean/Calculator/Store.lean` and its requests and responses `lean/Calculator/Wire.lean`,
// generated to the packages kernel, store and wire.
package calculator

import (
	"encoding/binary"
	"errors"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/go/calculator/kernel"
	"github.com/conao3/lean-leangage/go/calculator/store"
	"github.com/conao3/lean-leangage/go/calculator/wire"
	"github.com/conao3/lean-leangage/go/leangage"
	"github.com/conao3/lean-leangage/go/leangage/httpformat"
	"github.com/conao3/lean-leangage/go/leangage/pg"
	"github.com/conao3/lean-leangage/go/leangage/sql"
)

// Snapshot is one tenant's state, kept as a Lean value.
type Snapshot = leanfran.Value[kernel.Snapshot]

// WriteSet is the writes of an accepted command, kept as a Lean value.
type WriteSet = leanfran.Value[leanfran.OptionType[kernel.Memory]]

// Calculator implements the kernel contract, and the calculator's functions on the wire by
// passing each call on to the package wire.
type Calculator struct {
	scope *leanfran.ValueScope
}

// Engine is the memory engine of the calculator.
type Engine = leangage.MemoryEngine[kernel.Principal, Snapshot, kernel.Command, WriteSet, kernel.Reply, kernel.Error]

func NewEngine() *Engine {
	return leangage.NewMemoryEngine(Calculator{})
}

// PgEngine is the PostgreSQL engine of the calculator.
type PgEngine = pg.Engine[kernel.Principal, Snapshot, kernel.Command, WriteSet, kernel.Reply, kernel.Error]

// ConnectEngine is [pg.Connect] for the calculator.
func ConnectEngine(url string, size int, config pg.Config) (*PgEngine, error) {
	return pg.Connect(Calculator{}, url, size, config)
}

func must[T any](value T, err error) T {
	if err != nil {
		panic(err)
	}
	return value
}

func (c Calculator) Init() Snapshot {
	return kernel.Handle.In(c.scope).Init()
}

func (Calculator) Tenant(actor kernel.Principal) uint64 {
	return kernel.Tenant(actor)
}

func (Calculator) Scoped(
	region *leanfran.Region,
	run func(leangage.Kernel[kernel.Principal, Snapshot, kernel.Command, WriteSet, kernel.Reply, kernel.Error]),
) {
	region.WithValues(func(scope *leanfran.ValueScope) {
		run(Calculator{scope})
	})
}

func (c Calculator) Transition(
	actor kernel.Principal, snap Snapshot, cmd kernel.Command,
) (WriteSet, kernel.Reply, *kernel.Error) {
	values, handle := kernel.Value.In(c.scope), kernel.Handle.In(c.scope)
	who := values.NewPrincipal(actor)
	what := must(values.NewCommand(cmd))
	ws, reply, err := handle.Transition(who.Take(), snap.Borrow(), what.Take())
	if refusal, ok := errors.AsType[*leanfran.ExceptError[kernel.Error]](err); ok {
		return WriteSet{}, kernel.Reply{}, &refusal.Value
	}
	if err != nil {
		panic(err)
	}
	defer reply.CloseIn(c.scope)
	return ws, values.ReadReply(reply), nil
}

func (c Calculator) Apply(snap Snapshot, ws WriteSet) Snapshot {
	return kernel.Handle.In(c.scope).Apply(snap.Take(), ws.Take())
}

func (c Calculator) Release(snap Snapshot) {
	snap.CloseIn(c.scope)
}

func (Calculator) ReadOnly(cmd kernel.Command) bool {
	return must(kernel.ReadOnly(cmd))
}

func (Calculator) Tables() []sql.Tab {
	return store.Tables()
}

func (c Calculator) Load(rows [][][]sql.Val) (Snapshot, bool) {
	snap, err := store.Load(rows)
	if err != nil || snap == nil {
		return Snapshot{}, false
	}
	return must(kernel.Value.In(c.scope).NewSnapshot(*snap)), true
}

func (c Calculator) Writes(ws WriteSet) []sql.Write {
	return store.Writes(kernel.Value.In(c.scope).ReadOptionMemory(ws))
}

// EncodeStoredReply is the number in 8 bytes, most significant first, as the Rust calculator
// stores it.
func (Calculator) EncodeStoredReply(reply kernel.Reply) []byte {
	return binary.BigEndian.AppendUint64(nil, reply.V)
}

func (Calculator) DecodeStoredReply(stored []byte) (kernel.Reply, bool) {
	if len(stored) != 8 {
		return kernel.Reply{}, false
	}
	return kernel.Reply{V: binary.BigEndian.Uint64(stored)}, true
}

// Request is wire.Request.
func (Calculator) Request(
	tenant, user, expiry, now uint64, body httpformat.Body,
) (kernel.Principal, kernel.Command, *httpformat.Response) {
	call, err := wire.Request(tenant, user, expiry, now, body)
	if answer, ok := errors.AsType[*leanfran.ExceptError[httpformat.Response]](err); ok {
		return kernel.Principal{}, nil, &answer.Value
	}
	if err != nil {
		panic(err)
	}
	return call.Actor, call.Cmd, nil
}

// Respond is wire.Respond.
func (Calculator) Respond(reply kernel.Reply, refusal *kernel.Error) httpformat.Response {
	return wire.Respond(leanfran.Except[kernel.Error, kernel.Reply]{Error: refusal, Ok: reply})
}

// Fingerprint is wire.Fingerprint.
func (Calculator) Fingerprint(cmd kernel.Command) []byte {
	return must(wire.Fingerprint(cmd))
}

// Scope is wire.Scope.
func (Calculator) Scope(actor kernel.Principal) string {
	return wire.Scope(actor)
}
