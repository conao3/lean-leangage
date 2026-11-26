// Package leangage is the trusted server around a kernel proved in Lean: an engine that runs
// one command of a tenant at a time, bearer tokens, and the `/rpc` route. The package pg holds the engine
// that stores the snapshots in PostgreSQL.
package leangage

import (
	"errors"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/go/leangage/sql"
)

// Kernel is the contract of `Leangage.Kernel`, implemented by delegating to functions
// generated from Lean. Snapshot is one tenant's state as an engine stores it; a kernel that
// keeps it as a Lean value gives Apply the only reference, so Lean updates it in place, and
// keeps every Lean value of one snapshot in one [leanfran.Region].
type Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error any] interface {
	// Init is a tenant's snapshot before its first command.
	Init() Snapshot
	// Tenant is the only tenant the principal may read or write.
	Tenant(actor Principal) uint64
	// Transition decides a command. A non-nil error is a refusal; nothing is stored, and the
	// write set holds nothing to release.
	Transition(actor Principal, snap Snapshot, cmd Command) (WriteSet, Reply, *Error)
	// Apply consumes the snapshot and the writes and returns the next snapshot.
	Apply(snap Snapshot, ws WriteSet) Snapshot
	// Release consumes a snapshot the engine no longer keeps.
	Release(snap Snapshot)
	// Scoped runs one command's calls in the region: run gets a kernel whose calls hold the
	// region's lock and whose temporary values are released together when run returns. Calls
	// in different regions run in parallel; the snapshots passed to run's calls belong to the
	// region or to none.
	Scoped(region *leanfran.Region, run func(Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]))
}

// Storage is the contract of `Leangage.Storage`: how a kernel's snapshots are stored in
// PostgreSQL, implemented by delegating to functions generated from Lean, and the bytes an
// engine stores for a reply under an idempotency key. An engine calls these methods outside
// Scoped.
type Storage[Principal, Snapshot, Command, WriteSet, Reply, Error any] interface {
	Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]
	// ReadOnly is whether the command only reads: `ReadOnlySound` says it then writes nothing.
	ReadOnly(cmd Command) bool
	// Tables are the tables, in the order Load receives their rows.
	Tables() []sql.Tab
	// Load is the snapshot of the rows of each table; false when a row is not one the kernel
	// stores.
	Load(rows [][][]sql.Val) (Snapshot, bool)
	// Writes is the rows a write set stores; the write set is kept for Apply.
	Writes(ws WriteSet) []sql.Write
	// EncodeStoredReply is the stored form of a reply. Trusted: no theorem covers it.
	EncodeStoredReply(reply Reply) []byte
	// DecodeStoredReply is the reply EncodeStoredReply stored; false for bytes it does not
	// write.
	DecodeStoredReply(stored []byte) (Reply, bool)
}

// Why a request did not reach the kernel's decision, or its decision was not stored.
var (
	// ErrIdempotencyConflict: the idempotency key was used before with another command.
	ErrIdempotencyConflict = errors.New("idempotency key reused")
	// ErrStopped: the engine no longer runs commands: a command panicked while it held a
	// tenant's snapshot, or the engine was closed.
	ErrStopped = errors.New("engine stopped")
	// ErrRetriesExhausted: every attempt failed to serialize or lost its connection; none
	// committed, except that a request with an idempotency key may have committed on an attempt
	// whose COMMIT was lost.
	ErrRetriesExhausted = errors.New("retries exhausted")
	// ErrCommitUnknown: the connection was lost during the COMMIT of a request without an
	// idempotency key: it may or may not have committed.
	ErrCommitUnknown = errors.New("commit outcome unknown")
	// ErrDatabase wraps the error of the database, which failed the request; it did not commit.
	ErrDatabase = errors.New("database")
	// ErrBroken wraps why the stored rows or reply do not decode, a write set does not compile,
	// a read-only command wrote, or the request panicked. Nothing was committed.
	ErrBroken = errors.New("engine")
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
