// Package calculator is the calculator: the kernel is `lean/Calculator/Kernel.lean`, generated
// to the package kernel.
package calculator

import (
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"strconv"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leanharbor/go/calculator/kernel"
	"github.com/conao3/lean-leanharbor/go/leanharbor"
)

// Snapshot is one tenant's state, kept as a Lean value.
type Snapshot = leanfran.Value[kernel.Snapshot]

// WriteSet is the writes of an accepted command, kept as a Lean value.
type WriteSet = leanfran.Value[leanfran.OptionType[kernel.Memory]]

// Calculator implements the kernel contract and the wire format of the calculator.
type Calculator struct {
	scope *leanfran.ValueScope
}

// Engine is the memory engine of the calculator.
type Engine = leanharbor.MemoryEngine[kernel.Principal, Snapshot, kernel.Command, WriteSet, kernel.Reply, kernel.Error]

func NewEngine() *Engine {
	return leanharbor.NewMemoryEngine(Calculator{})
}

func must[T any](value T, err error) T {
	if err != nil {
		panic(err)
	}
	return value
}

func (Calculator) Init() Snapshot {
	return kernel.Handle.Init()
}

func (Calculator) Tenant(actor kernel.Principal) uint64 {
	return kernel.Tenant(actor)
}

func (Calculator) Scoped(run func(leanharbor.Kernel[kernel.Principal, Snapshot, kernel.Command, WriteSet, kernel.Reply, kernel.Error])) {
	leanfran.WithValues(func(scope *leanfran.ValueScope) {
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
	var refusal *leanfran.ExceptError[kernel.Error]
	if errors.As(err, &refusal) {
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

func (Calculator) Principal(tenant, user uint64) kernel.Principal {
	return kernel.Principal{Org: tenant, User: user}
}

func number(fields map[string]json.RawMessage, name string) (uint64, error) {
	value, err := strconv.ParseUint(string(fields[name]), 10, 64)
	if err != nil {
		return 0, fmt.Errorf("`%s` must be an integer below 2^64", name)
	}
	return value, nil
}

func only(fields map[string]json.RawMessage, names ...string) bool {
	for _, name := range names {
		if _, ok := fields[name]; !ok {
			return false
		}
	}
	return len(fields) == len(names)+1
}

// OpNamed is the operation with the given name on the wire.
func OpNamed(name string) (kernel.Op, bool) {
	switch name {
	case "add":
		return kernel.OpAdd(), true
	case "sub":
		return kernel.OpSub(), true
	case "mul":
		return kernel.OpMul(), true
	case "div":
		return kernel.OpDiv(), true
	}
	return kernel.Op{}, false
}

func (Calculator) DecodeCommand(body []byte) (kernel.Command, error) {
	var fields map[string]json.RawMessage
	if err := json.Unmarshal(body, &fields); err != nil || fields == nil {
		return nil, errors.New("not a calculator command")
	}
	var name string
	if raw, ok := fields["cmd"]; !ok {
		return nil, errors.New("missing field `cmd`")
	} else if err := json.Unmarshal(raw, &name); err != nil {
		return nil, errors.New("not a calculator command")
	}
	switch {
	case name == "set" && only(fields, "value"):
		value, err := number(fields, "value")
		return kernel.CommandSet{Value: value}, err
	case name == "apply" && only(fields, "op", "arg"):
		var op string
		if err := json.Unmarshal(fields["op"], &op); err != nil {
			return nil, errors.New("not a calculator command")
		}
		if found, ok := OpNamed(op); ok {
			arg, err := number(fields, "arg")
			return kernel.CommandApply{Op: found, Arg: arg}, err
		}
	case name == "get" && only(fields):
		return kernel.CommandGet{}, nil
	}
	return nil, errors.New("not a calculator command")
}

func (Calculator) EncodeReply(reply kernel.Reply) []byte {
	return kernel.EncodeReplyArray(reply)
}

func (Calculator) EncodeError(refusal kernel.Error) (int, []byte) {
	return http.StatusUnprocessableEntity, kernel.EncodeErrorArray(refusal)
}

func (Calculator) Fingerprint(cmd kernel.Command) []byte {
	return fmt.Appendf(nil, "%#v", cmd)
}

func (Calculator) Scope(actor kernel.Principal) string {
	return fmt.Sprintf("u%d", actor.User)
}
