package leanharbor

import (
	"bytes"
	"sync"
)

type slot struct {
	tenant uint64
	scope  string
	key    string
}

type stored[Reply any] struct {
	fingerprint []byte
	reply       Reply
}

// MemoryEngine keeps every tenant's snapshot in this process, under one lock: commands run one
// at a time, on the caller's goroutine.
type MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error any] struct {
	kernel  Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]
	mu      sync.Mutex
	tenants map[uint64]Snapshot
	replies map[slot]stored[Reply]
	stopped bool
}

func NewMemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error any](
	kernel Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error],
) *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error] {
	return &MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]{
		kernel:  kernel,
		tenants: map[uint64]Snapshot{},
		replies: map[slot]stored[Reply]{},
	}
}

func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) run(
	tenant uint64, actor Principal, cmd Command,
) (Reply, *Error) {
	snap, ok := e.tenants[tenant]
	if !ok {
		snap = e.kernel.Init()
		e.tenants[tenant] = snap
	}
	var reply Reply
	var refusal *Error
	e.kernel.Scoped(func(kernel Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]) {
		var ws WriteSet
		ws, reply, refusal = kernel.Transition(actor, snap, cmd)
		if refusal == nil {
			e.tenants[tenant] = kernel.Apply(snap, ws)
		}
	})
	return reply, refusal
}

func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) execute(
	actor Principal, cmd Command, idempotency *Idempotency,
) (Reply, *Error, error) {
	tenant := e.kernel.Tenant(actor)
	if idempotency == nil {
		reply, refusal := e.run(tenant, actor, cmd)
		return reply, refusal, nil
	}
	at := slot{tenant, idempotency.Scope, idempotency.Key}
	if found, ok := e.replies[at]; ok {
		if !bytes.Equal(found.fingerprint, idempotency.Fingerprint) {
			var zero Reply
			return zero, nil, ErrIdempotencyConflict
		}
		return found.reply, nil, nil
	}
	reply, refusal := e.run(tenant, actor, cmd)
	if refusal == nil {
		e.replies[at] = stored[Reply]{idempotency.Fingerprint, reply}
	}
	return reply, refusal, nil
}

// Inspect shows f the tenant's snapshot; it reports false before the tenant's first command.
func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Inspect(
	tenant uint64, f func(Snapshot),
) bool {
	e.mu.Lock()
	defer e.mu.Unlock()
	snap, ok := e.tenants[tenant]
	if ok {
		f(snap)
	}
	return ok
}

func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Execute(
	actor Principal, cmd Command, idempotency *Idempotency,
) (Reply, *Error, error) {
	e.mu.Lock()
	defer e.mu.Unlock()
	if e.stopped {
		var zero Reply
		return zero, nil, ErrStopped
	}
	e.stopped = true
	reply, refusal, err := e.execute(actor, cmd, idempotency)
	e.stopped = false
	return reply, refusal, err
}
