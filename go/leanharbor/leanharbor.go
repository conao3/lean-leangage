// Package leanharbor is the trusted shell around a kernel proved in Lean: an engine that runs
// one command at a time, bearer tokens, and the `/rpc` route.
package leanharbor

import "errors"

// Kernel is the contract of `Leanharbor.Kernel`, implemented by delegating to functions
// generated from Lean. Snapshot is one tenant's state as an engine stores it; a kernel that
// keeps it as a Lean value gives Apply the only reference, so Lean updates it in place.
type Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error any] interface {
	// Init is a tenant's snapshot before its first command.
	Init() Snapshot
	// Tenant is the only tenant the principal may read or write.
	Tenant(actor Principal) uint64
	// Transition decides a command. A non-nil error is a refusal; nothing is stored.
	Transition(actor Principal, snap Snapshot, cmd Command) (WriteSet, Reply, *Error)
	// Apply consumes the snapshot and the writes and returns the next snapshot.
	Apply(snap Snapshot, ws WriteSet) Snapshot
	// Scoped runs one command's calls: run gets a kernel whose temporary values are released
	// together when run returns.
	Scoped(run func(Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]))
}

// Why a request did not reach the kernel's decision.
var (
	// ErrIdempotencyConflict: the idempotency key was used before with another command.
	ErrIdempotencyConflict = errors.New("idempotency key reused")
	// ErrStopped: the engine no longer runs commands: a command panicked while it held the
	// snapshots.
	ErrStopped = errors.New("engine stopped")
)

// Idempotency is the scope, key and fingerprint of a request that carries an idempotency key.
type Idempotency struct {
	Scope       string
	Key         string
	Fingerprint []byte
}

// Engine runs commands. The error is the engine's, the refusal the kernel's decision.
type Engine[Principal, Command, Reply, Error any] interface {
	// Execute runs the command. With idempotency, it runs it once per (tenant, scope, key): a
	// repeat with the same fingerprint returns the stored reply. Refusals are not stored.
	Execute(actor Principal, cmd Command, idempotency *Idempotency) (Reply, *Error, error)
}
