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
	ws, reply, refusal := e.kernel.Transition(actor, snap, cmd)
	if refusal != nil {
		return reply, refusal
	}
	e.tenants[tenant] = e.kernel.Apply(snap, ws)
	return reply, nil
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
