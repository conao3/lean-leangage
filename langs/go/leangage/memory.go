package leangage

import (
	"bytes"
	"sync"
	"sync/atomic"

	"github.com/conao3/leanfran-go"
)

type slot struct {
	scope string
	key   string
}

type stored[Reply any] struct {
	fingerprint []byte
	reply       Reply
}

// tenant is one tenant's snapshot, in a region of its own, and the replies stored under its
// idempotency keys. mu is held across each of the tenant's commands.
type tenant[Snapshot, Reply any] struct {
	mu      sync.Mutex
	region  *leanfran.Region
	snap    Snapshot
	ready   bool
	replies map[slot]stored[Reply]
}

// MemoryEngine keeps every tenant's snapshot in this process, each in a [leanfran.Region] of
// its own. The commands of one tenant run one at a time and those of different tenants in
// parallel, on the callers' goroutines; a lock held only to look a tenant up guards the table
// of tenants.
type MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error any] struct {
	kernel  Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]
	mu      sync.Mutex
	tenants map[uint64]*tenant[Snapshot, Reply]
	stopped atomic.Bool
}

func NewMemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error any](
	kernel Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error],
) *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error] {
	return &MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]{
		kernel:  kernel,
		tenants: map[uint64]*tenant[Snapshot, Reply]{},
	}
}

// lookup is the tenant's entry, created when create is set; nil when it is not and the tenant
// has none.
func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) lookup(
	id uint64, create bool,
) *tenant[Snapshot, Reply] {
	e.mu.Lock()
	defer e.mu.Unlock()
	t, ok := e.tenants[id]
	if !ok && create {
		t = &tenant[Snapshot, Reply]{region: leanfran.NewRegion(), replies: map[slot]stored[Reply]{}}
		e.tenants[id] = t
	}
	return t
}

func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) run(
	t *tenant[Snapshot, Reply], actor Principal, cmd Command,
) (Reply, *Error) {
	var reply Reply
	var refusal *Error
	e.kernel.Scoped(t.region, func(kernel Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]) {
		if !t.ready {
			t.snap = kernel.Init()
			t.ready = true
		}
		var ws WriteSet
		ws, reply, refusal = kernel.Transition(actor, t.snap, cmd)
		if refusal == nil {
			t.snap = kernel.Apply(t.snap, ws)
		}
	})
	return reply, refusal
}

func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) execute(
	t *tenant[Snapshot, Reply], actor Principal, cmd Command, idempotency *Idempotency,
) (Reply, *Error, error) {
	if idempotency == nil {
		reply, refusal := e.run(t, actor, cmd)
		return reply, refusal, nil
	}
	at := slot{idempotency.Scope, idempotency.Key}
	if found, ok := t.replies[at]; ok {
		if !bytes.Equal(found.fingerprint, idempotency.Fingerprint) {
			var zero Reply
			return zero, nil, ErrIdempotencyConflict
		}
		return found.reply, nil, nil
	}
	reply, refusal := e.run(t, actor, cmd)
	if refusal == nil {
		t.replies[at] = stored[Reply]{idempotency.Fingerprint, reply}
	}
	return reply, refusal, nil
}

// Inspect shows f the tenant's snapshot; it reports false before the tenant's first command.
func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Inspect(
	id uint64, f func(Snapshot),
) bool {
	t := e.lookup(id, false)
	if t == nil {
		return false
	}
	t.mu.Lock()
	defer t.mu.Unlock()
	if t.ready {
		f(t.snap)
	}
	return t.ready
}

func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Execute(
	actor Principal, cmd Command, idempotency *Idempotency,
) (Reply, *Error, error) {
	t := e.lookup(e.kernel.Tenant(actor), true)
	t.mu.Lock()
	defer t.mu.Unlock()
	if e.stopped.Load() {
		var zero Reply
		return zero, nil, ErrStopped
	}
	finished := false
	defer func() {
		if !finished {
			e.stopped.Store(true)
		}
	}()
	reply, refusal, err := e.execute(t, actor, cmd, idempotency)
	finished = true
	return reply, refusal, err
}

// Close stops the engine and releases every tenant's snapshot. It waits for the commands that
// run; later ones fail with [ErrStopped].
func (e *MemoryEngine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Close() {
	e.mu.Lock()
	defer e.mu.Unlock()
	e.stopped.Store(true)
	for _, t := range e.tenants {
		t.mu.Lock()
		if t.ready {
			e.kernel.Release(t.snap)
			var zero Snapshot
			t.snap, t.ready = zero, false
		}
		t.mu.Unlock()
	}
}
