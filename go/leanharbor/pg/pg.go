// Package pg is an engine that stores each tenant's snapshot in PostgreSQL, as
// `Leanharbor.Storage.Stored` describes. It is trusted: no theorem covers this package.
//
// At start it creates the kernel's tables with the statements of the generated Create and
// Render. Each command runs in one SERIALIZABLE transaction: it reads the tenant's rows with the
// generated Select of every table, builds the snapshot with the kernel's Load, calls Transition,
// and sends the statements the generated Compile makes of the generated Plan of each write. The
// only other statements are the constant ones of this file: the transaction control, the
// advisory locks, and the framework's table leanharbor_idempotency. They are the statements of
// the Rust engine `rust/leanharbor-pg`, so the two engines share a database.
//
// The contract (the engine's side of `Storage.Stored`):
//
//  1. One attempt reads one tenant, calls Transition, writes and commits in one SERIALIZABLE
//     transaction.
//  2. A retry opens a new transaction, reads the rows again and calls Transition again. An
//     attempt is retried after a lost connection, SQLSTATE 40001, 40P01, 57P01, 57P02 or 53200
//     from a full table of serializable conflicts, and, with an idempotency key, 23505 and a lost
//     COMMIT; at most [Config.MaxAttempts] attempts, 20 by default.
//  3. A refused command rolls back and writes no row.
//  4. The app's writes and the reply stored under an idempotency key commit in one transaction.
//  5. The tenant's advisory lock is taken before BEGIN and released before the connection
//     returns to the pool; a connection that fails to release it is closed.
//  6. A command ReadOnly accepts runs in a SERIALIZABLE READ ONLY DEFERRABLE transaction,
//     without the advisory lock and without an idempotency key (a keyed request takes the write
//     path), and fails if its write set stores a row.
//  7. A request without an idempotency key whose connection is lost during COMMIT, or whose
//     COMMIT fails with 57P01 or 57P02, fails with [leanharbor.ErrCommitUnknown].
//
// Execute takes no context: every attempt runs on the caller's goroutine to its end, so a caller
// that stops waiting (a closed HTTP connection) does not interrupt an attempt between its lock
// and its unlock. The pool and the connections stay inside this package.
package pg

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"math/big"
	"math/rand/v2"
	"sync/atomic"
	"time"

	"github.com/jackc/pgx/v5"
	"github.com/jackc/pgx/v5/pgconn"
	"github.com/jackc/pgx/v5/pgtype"
	"github.com/jackc/pgx/v5/pgxpool"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leanharbor/go/leanharbor"
	"github.com/conao3/lean-leanharbor/go/leanharbor/sql"
)

// The replies of the commands run under an idempotency key, per tenant, scope and key.
const frameworkDDL = "CREATE TABLE IF NOT EXISTS leanharbor_idempotency (" +
	"tenant_id BIGINT NOT NULL, scope TEXT NOT NULL, key TEXT NOT NULL, " +
	"fingerprint BYTEA NOT NULL, reply BYTEA NOT NULL, PRIMARY KEY (tenant_id, scope, key))"

var frameworkTables = []string{"leanharbor_idempotency"}

const (
	storedReply = "SELECT fingerprint, reply FROM leanharbor_idempotency " +
		"WHERE tenant_id = $1 AND scope = $2 AND key = $3"
	storeReply = "INSERT INTO leanharbor_idempotency " +
		"(tenant_id, scope, key, fingerprint, reply) VALUES ($1, $2, $3, $4, $5)"
	// Held while the tables are created, so that engines starting together do not race in
	// CREATE TABLE. The two-key form, whose keys never meet a tenant's lock.
	schemaLock   = "SELECT pg_advisory_lock(1819173234, 0)"
	schemaUnlock = "SELECT pg_advisory_unlock(1819173234, 0)"
	// The tenant's lock: the tenant id as a BIGINT.
	tenantLock = "SELECT pg_advisory_lock($1)"
	unlockAll  = "SELECT pg_advisory_unlock_all()"
	backendPid = "SELECT pg_backend_pid()"
	txInfo     = "SELECT pg_backend_pid(), current_setting('transaction_isolation'), " +
		"current_setting('transaction_read_only'), current_setting('transaction_deferrable'), " +
		"(SELECT virtualxid FROM pg_locks WHERE locktype = 'virtualxid' AND pid = pg_backend_pid())"
	beginWrite = "START TRANSACTION ISOLATION LEVEL SERIALIZABLE"
	beginRead  = "START TRANSACTION ISOLATION LEVEL SERIALIZABLE, READ ONLY, DEFERRABLE"
	commit     = "COMMIT"
	rollback   = "ROLLBACK"
)

// Point is a point of an attempt where [Config.Hook] is called.
type Point int

const (
	// Locked is before BEGIN, holding the tenant's advisory lock if [Config.TenantLock]. Not on
	// the read-only path.
	Locked Point = iota
	// Loaded: the rows are read, Transition has not run.
	Loaded
	// Written: the writes and the stored reply are sent, COMMIT is not. Not on the read-only
	// path.
	Written
)

func (p Point) String() string {
	switch p {
	case Locked:
		return "Locked"
	case Loaded:
		return "Loaded"
	case Written:
		return "Written"
	}
	return fmt.Sprintf("Point(%d)", int(p))
}

// TxInfo is the transaction of an attempt, as PostgreSQL reports it.
type TxInfo struct {
	Vxid       string
	Isolation  string
	ReadOnly   bool
	Deferrable bool
}

// Attempt is where an attempt is when [Config.Hook] is called.
type Attempt struct {
	Point  Point
	Tenant uint64
	// Pid is the process of the attempt's connection.
	Pid int32
	// Tx is set from [Loaded] on.
	Tx *TxInfo
}

// Hook is called at each [Point] of each attempt, which waits for it to return. For tests that
// inject faults.
type Hook func(Attempt)

type Config struct {
	// MaxAttempts is the number of attempts of one command before
	// [leanharbor.ErrRetriesExhausted].
	MaxAttempts int
	// TenantLock takes the tenant's advisory lock before each write attempt. It spares retries;
	// SERIALIZABLE keeps the commits serial without it.
	TenantLock bool
	Hook       Hook
}

// DefaultConfig is 20 attempts with the tenant's lock and no hook.
func DefaultConfig() Config {
	return Config{MaxAttempts: 20, TenantLock: true}
}

// Stats is what the engine did, counted since it started.
type Stats struct {
	Attempts uint64
	Retries  uint64
	// Commits are the accepted commands committed, on both paths.
	Commits uint64
	// Replays are the requests answered with a stored reply.
	Replays uint64
	// Reads are the attempts on the read-only path, also counted in Attempts.
	Reads uint64
}

type stats struct {
	attempts, retries, commits, replays, reads atomic.Uint64
}

type failureKind int

const (
	// The attempt did not commit.
	failPostgres failureKind = iota
	// The connection was lost before COMMIT: the attempt did not commit.
	failLost
	// No connection: the attempt did not start.
	failPool
	// The connection was lost during COMMIT.
	failCommitLost
	// Retrying cannot help.
	failFinal
)

// failure is why an attempt ended without a decision to return.
type failure struct {
	kind failureKind
	err  error
}

func broken(message string) *failure {
	return &failure{failFinal, fmt.Errorf("%w: %s", leanharbor.ErrBroken, message)}
}

func code(err error) string {
	var pgErr *pgconn.PgError
	if errors.As(err, &pgErr) {
		return pgErr.Code
	}
	return ""
}

// ssiExhausted: SERIALIZABLE ran out of its shared memory for conflicts; PostgreSQL aborted the
// transaction.
func ssiExhausted(err error) bool {
	var pgErr *pgconn.PgError
	return errors.As(err, &pgErr) && pgErr.Code == "53200" &&
		(bytes.Contains([]byte(pgErr.Message), []byte("RWConflictPool")) ||
			bytes.Contains([]byte(pgErr.Hint), []byte("max_pred_locks_per_transaction")))
}

// lost is the failure of a statement on c: a lost connection if c closed without a server's
// error code, else the database's.
func lost(c *pgxpool.Conn, err error) *failure {
	if code(err) == "" && c.Conn().IsClosed() {
		return &failure{failLost, err}
	}
	return &failure{failPostgres, err}
}

// commitFailure: a COMMIT that failed without a server's error code, or because the server
// ended the connection, may have committed.
func commitFailure(err error) *failure {
	switch code(err) {
	case "", "57P01", "57P02":
		return &failure{failCommitLost, err}
	}
	return &failure{failPostgres, err}
}

func (f *failure) retryable(keyed bool) bool {
	switch f.kind {
	case failPool, failLost:
		return true
	case failPostgres:
		switch code(f.err) {
		case "40001", "40P01", "57P01", "57P02":
			return true
		case "23505":
			return keyed
		}
		return ssiExhausted(f.err)
	case failCommitLost:
		return keyed
	}
	return false
}

func (f *failure) engineError() error {
	switch f.kind {
	case failCommitLost:
		return leanharbor.ErrCommitUnknown
	case failFinal:
		return f.err
	}
	return fmt.Errorf("%w: %w", leanharbor.ErrDatabase, f.err)
}

func database(err error) error {
	return fmt.Errorf("%w: %w", leanharbor.ErrDatabase, err)
}

// nonNil is b, or an empty slice for nil, which pgx would send as NULL.
func nonNil(b []byte) []byte {
	if b == nil {
		return []byte{}
	}
	return b
}

// arguments are the values as parameters of the types PostgreSQL inferred for them.
func arguments(types *pgtype.Map, oids []uint32, vals []sql.Val) ([]any, error) {
	if len(oids) != len(vals) {
		return nil, fmt.Errorf("%d values for %d parameters", len(vals), len(oids))
	}
	args := make([]any, len(vals))
	for i, val := range vals {
		oid := oids[i]
		switch v := val.(type) {
		case sql.ValInt:
			if oid == pgtype.Int8OID {
				args[i] = v.V
				continue
			}
		case sql.ValBool:
			if oid == pgtype.BoolOID {
				args[i] = v.V
				continue
			}
		case sql.ValText:
			if oid == pgtype.TextOID {
				args[i] = v.V
				continue
			}
		case sql.ValBytes:
			if oid == pgtype.ByteaOID {
				args[i] = nonNil(v.V)
				continue
			}
		case sql.ValNull:
			args[i] = nil
			continue
		}
		return nil, fmt.Errorf("%#v as a parameter of type %s", val, typeName(types, oid))
	}
	return args, nil
}

func typeName(types *pgtype.Map, oid uint32) string {
	if t, ok := types.TypeForOID(oid); ok {
		return t.Name
	}
	return fmt.Sprintf("oid %d", oid)
}

// values is a row as values, by the type of each column.
func values(types *pgtype.Map, fields []pgconn.FieldDescription, row []any) ([]sql.Val, *failure) {
	vals := make([]sql.Val, len(row))
	for i, field := range fields {
		if row[i] == nil {
			vals[i] = sql.ValNull{}
			continue
		}
		var val sql.Val
		switch v := row[i].(type) {
		case int64:
			if field.DataTypeOID == pgtype.Int8OID {
				val = sql.ValInt{V: v}
			}
		case bool:
			if field.DataTypeOID == pgtype.BoolOID {
				val = sql.ValBool{V: v}
			}
		case string:
			if field.DataTypeOID == pgtype.TextOID {
				val = sql.ValText{V: v}
			}
		case []byte:
			if field.DataTypeOID == pgtype.ByteaOID {
				val = sql.ValBytes{V: v}
			}
		}
		if val == nil {
			return nil, broken("a column of type " + typeName(types, field.DataTypeOID))
		}
		vals[i] = val
	}
	return vals, nil
}

type statement struct {
	text   string
	params []sql.Val
}

// decision is what Transition decided, with the statements that store an accepted command's
// writes.
type decision[Reply, Error any] struct {
	refusal    *Error
	statements []statement
	reply      Reply
}

func backoff(attempt int) time.Duration {
	limit := int64(1000) << min(attempt, 8)
	return time.Duration(rand.Int64N(limit)+100) * time.Microsecond
}

// Engine is a pool of connections to one database.
type Engine[Principal, Snapshot, Command, WriteSet, Reply, Error any] struct {
	storage leanharbor.Storage[Principal, Snapshot, Command, WriteSet, Reply, Error]
	pool    *pgxpool.Pool
	tables  []sql.Tab
	config  Config
	stats   stats
}

var background = context.Background()

func render(q sql.Sql) (string, error) {
	return sql.Render(q)
}

func valid(tables []sql.Tab) bool {
	ok, err := sql.Valid(tables)
	return err == nil && ok
}

// create runs the generated Create of each table and the framework's table under the schema's
// lock.
func create(conn *pgx.Conn, tables []sql.Tab) error {
	if _, err := conn.Exec(background, schemaLock); err != nil {
		return err
	}
	created := func() error {
		if _, err := conn.Exec(background, frameworkDDL); err != nil {
			return err
		}
		for _, t := range tables {
			q, err := sql.Create(t)
			if err != nil {
				return err
			}
			text, err := render(q)
			if err != nil {
				return err
			}
			if _, err := conn.Exec(background, text); err != nil {
				return err
			}
		}
		return nil
	}()
	if _, err := conn.Exec(background, schemaUnlock); err != nil {
		return err
	}
	return created
}

// Connect opens a pool of up to size connections to url and creates the tables that do not
// exist, with the generated Create of each of storage.Tables() and the framework's table. url
// is a connection string pgx reads, with the PG* environment variables as its defaults.
func Connect[Principal, Snapshot, Command, WriteSet, Reply, Error any](
	storage leanharbor.Storage[Principal, Snapshot, Command, WriteSet, Reply, Error],
	url string, size int, config Config,
) (*Engine[Principal, Snapshot, Command, WriteSet, Reply, Error], error) {
	tables := storage.Tables()
	if !valid(tables) {
		return nil, fmt.Errorf("%w: the tables are not valid", leanharbor.ErrBroken)
	}
	poolConfig, err := pgxpool.ParseConfig(url)
	if err != nil {
		return nil, database(err)
	}
	poolConfig.MaxConns = int32(size)
	conn, err := pgx.ConnectConfig(background, poolConfig.ConnConfig.Copy())
	if err != nil {
		return nil, database(err)
	}
	created := create(conn, tables)
	_ = conn.Close(background)
	if created != nil {
		return nil, database(created)
	}
	pool, err := pgxpool.NewWithConfig(background, poolConfig)
	if err != nil {
		return nil, database(err)
	}
	return &Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]{
		storage: storage,
		pool:    pool,
		tables:  tables,
		config:  config,
	}, nil
}

// Close closes the pool's connections.
func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Close() {
	e.pool.Close()
}

func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Stats() Stats {
	return Stats{
		Attempts: e.stats.attempts.Load(),
		Retries:  e.stats.retries.Load(),
		Commits:  e.stats.commits.Load(),
		Replays:  e.stats.replays.Load(),
		Reads:    e.stats.reads.Load(),
	}
}

// Idle is the number of connections open and idle in the pool.
func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Idle() int {
	return int(e.pool.Stat().IdleConns())
}

func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) fireLocked(
	c *pgxpool.Conn, tenant uint64,
) *failure {
	if e.config.Hook == nil {
		return nil
	}
	var pid int32
	if err := c.QueryRow(background, backendPid).Scan(&pid); err != nil {
		return lost(c, err)
	}
	e.config.Hook(Attempt{Point: Locked, Tenant: tenant, Pid: pid})
	return nil
}

func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) fire(
	c *pgxpool.Conn, point Point, tenant uint64,
) *failure {
	if e.config.Hook == nil {
		return nil
	}
	var pid int32
	var info TxInfo
	var readOnly, deferrable string
	err := c.QueryRow(background, txInfo).Scan(&pid, &info.Isolation, &readOnly, &deferrable, &info.Vxid)
	if err != nil {
		return lost(c, err)
	}
	info.ReadOnly = readOnly == "on"
	info.Deferrable = deferrable == "on"
	e.config.Hook(Attempt{Point: point, Tenant: tenant, Pid: pid, Tx: &info})
	return nil
}

// prepared is the statement text prepared on c, and its values as parameters.
func prepared(c *pgxpool.Conn, text string, vals []sql.Val) ([]any, error) {
	sd, err := c.Conn().Prepare(background, text, text)
	if err != nil {
		return nil, err
	}
	return arguments(c.Conn().TypeMap(), sd.ParamOIDs, vals)
}

// load is the rows of every table for the tenant, by the generated Select.
func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) load(
	c *pgxpool.Conn, tv int64,
) ([][][]sql.Val, *failure) {
	all := make([][][]sql.Val, 0, len(e.tables))
	for t := range e.tables {
		selected, err := sql.Select(e.tables, tv, big.NewInt(int64(t)), nil)
		if err != nil || selected == nil {
			return nil, broken("a table has no SELECT")
		}
		text, err := render(selected.Fst)
		if err != nil {
			return nil, broken("a SELECT does not render")
		}
		args, err := prepared(c, text, selected.Snd)
		if err != nil {
			return nil, lost(c, err)
		}
		rows, err := c.Query(background, text, args...)
		if err != nil {
			return nil, lost(c, err)
		}
		table := [][]sql.Val{}
		for rows.Next() {
			row, err := rows.Values()
			if err != nil {
				rows.Close()
				return nil, lost(c, err)
			}
			vals, f := values(c.Conn().TypeMap(), rows.FieldDescriptions(), row)
			if f != nil {
				rows.Close()
				return nil, f
			}
			table = append(table, vals)
		}
		if err := rows.Err(); err != nil {
			return nil, lost(c, err)
		}
		all = append(all, table)
	}
	return all, nil
}

// decide loads the snapshot, runs the command on it and compiles its writes. It sends no
// statement, so the lock of the region that Scoped holds is held for no query. Each request
// has a region of its own, so the requests decide in parallel.
func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) decide(
	tv int64, rows [][][]sql.Val, actor Principal, cmd Command,
) (decision[Reply, Error], *failure) {
	var d decision[Reply, Error]
	snap, ok := e.storage.Load(rows)
	if !ok {
		return d, broken("the stored rows do not load")
	}
	var ws WriteSet
	region := leanfran.NewRegion()
	e.storage.Scoped(region, func(k leanharbor.Kernel[Principal, Snapshot, Command, WriteSet, Reply, Error]) {
		ws, d.reply, d.refusal = k.Transition(actor, snap, cmd)
		k.Release(snap)
	})
	if d.refusal != nil {
		return d, nil
	}
	for _, write := range e.storage.Writes(ws) {
		stmt, err := sql.Plan(write)
		if err != nil {
			return d, broken("a write does not compile")
		}
		compiled, err := sql.Compile(e.tables, tv, stmt)
		if err != nil || compiled == nil {
			return d, broken("a write does not compile")
		}
		text, err := render(compiled.Fst)
		if err != nil {
			return d, broken("a write does not render")
		}
		d.statements = append(d.statements, statement{text, compiled.Snd})
	}
	return d, nil
}

type outcome[Reply, Error any] struct {
	reply   Reply
	refusal *Error
}

// Execute runs the command. A panic of the kernel or the engine fails the request with
// [leanharbor.ErrBroken]; the attempt's connection is closed.
func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) Execute(
	actor Principal, cmd Command, idempotency *leanharbor.Idempotency,
) (reply Reply, refusal *Error, err error) {
	defer func() {
		if p := recover(); p != nil {
			var zero Reply
			reply, refusal, err = zero, nil, fmt.Errorf("%w: the request failed: %v", leanharbor.ErrBroken, p)
		}
	}()
	read := idempotency == nil && e.storage.ReadOnly(cmd)
	keyed := idempotency != nil
	for attempt := range e.config.MaxAttempts {
		e.stats.attempts.Add(1)
		var out outcome[Reply, Error]
		var f *failure
		if read {
			e.stats.reads.Add(1)
			out, f = e.readAttempt(actor, cmd)
		} else {
			out, f = e.writeAttempt(actor, cmd, idempotency)
		}
		if f == nil {
			return out.reply, out.refusal, nil
		}
		if !f.retryable(keyed) {
			var zero Reply
			return zero, nil, f.engineError()
		}
		e.stats.retries.Add(1)
		time.Sleep(backoff(attempt))
	}
	var zero Reply
	return zero, nil, leanharbor.ErrRetriesExhausted
}

// release returns c to the pool when the attempt ended without a failure and holds no advisory
// lock, and closes it otherwise.
func release(c *pgxpool.Conn, clean bool) {
	if clean {
		c.Release()
		return
	}
	ctx, cancel := context.WithTimeout(background, 5*time.Second)
	defer cancel()
	_ = c.Hijack().Close(ctx)
}

// writeAttempt is one attempt on a connection of its own.
func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) writeAttempt(
	actor Principal, cmd Command, idempotency *leanharbor.Idempotency,
) (outcome[Reply, Error], *failure) {
	tenant := e.storage.Tenant(actor)
	tv := int64(tenant)
	c, err := e.pool.Acquire(background)
	if err != nil {
		return outcome[Reply, Error]{}, &failure{failPool, err}
	}
	ended := false
	var f *failure
	defer func() {
		unlocked := true
		if e.config.TenantLock {
			_, err := c.Exec(background, unlockAll)
			unlocked = err == nil
		}
		release(c, ended && f == nil && unlocked)
	}()
	var out outcome[Reply, Error]
	if e.config.TenantLock {
		if _, err := c.Exec(background, tenantLock, tv); err != nil {
			f = lost(c, err)
		}
	}
	if f == nil {
		f = e.fireLocked(c, tenant)
	}
	if f == nil {
		out, f = e.transact(c, actor, cmd, idempotency, tv)
	}
	ended = true
	return out, f
}

func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) transact(
	c *pgxpool.Conn, actor Principal, cmd Command, idempotency *leanharbor.Idempotency, tv int64,
) (outcome[Reply, Error], *failure) {
	var out outcome[Reply, Error]
	tenant := e.storage.Tenant(actor)
	if _, err := c.Exec(background, beginWrite); err != nil {
		return out, lost(c, err)
	}
	if idempotency != nil {
		var fingerprint, stored []byte
		err := c.QueryRow(background, storedReply, tv, idempotency.Scope, idempotency.Key).
			Scan(&fingerprint, &stored)
		switch {
		case errors.Is(err, pgx.ErrNoRows):
		case err != nil:
			return out, lost(c, err)
		default:
			if !bytes.Equal(fingerprint, idempotency.Fingerprint) {
				if _, err := c.Exec(background, rollback); err != nil {
					return out, lost(c, err)
				}
				return out, &failure{failFinal, leanharbor.ErrIdempotencyConflict}
			}
			reply, ok := e.storage.DecodeStoredReply(stored)
			if !ok {
				return out, broken("a stored reply does not decode")
			}
			if _, err := c.Exec(background, rollback); err != nil {
				return out, lost(c, err)
			}
			e.stats.replays.Add(1)
			out.reply = reply
			return out, nil
		}
	}
	rows, f := e.load(c, tv)
	if f != nil {
		return out, f
	}
	if f := e.fire(c, Loaded, tenant); f != nil {
		return out, f
	}
	d, f := e.decide(tv, rows, actor, cmd)
	if f != nil {
		return out, f
	}
	if d.refusal != nil {
		if _, err := c.Exec(background, rollback); err != nil {
			return out, lost(c, err)
		}
		out.refusal = d.refusal
		return out, nil
	}
	for _, s := range d.statements {
		args, err := prepared(c, s.text, s.params)
		if err != nil {
			return out, lost(c, err)
		}
		if _, err := c.Exec(background, s.text, args...); err != nil {
			return out, lost(c, err)
		}
	}
	if idempotency != nil {
		stored := nonNil(e.storage.EncodeStoredReply(d.reply))
		_, err := c.Exec(background, storeReply, tv, idempotency.Scope, idempotency.Key,
			nonNil(idempotency.Fingerprint), stored)
		if err != nil {
			return out, lost(c, err)
		}
	}
	if f := e.fire(c, Written, tenant); f != nil {
		return out, f
	}
	tag, err := c.Exec(background, commit)
	if err != nil {
		return out, commitFailure(err)
	}
	if tag.String() != commit {
		return out, &failure{failPostgres, fmt.Errorf("COMMIT answered %s", tag)}
	}
	e.stats.commits.Add(1)
	out.reply = d.reply
	return out, nil
}

// readAttempt is one attempt on the read-only path, on a connection of its own.
func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) readAttempt(
	actor Principal, cmd Command,
) (outcome[Reply, Error], *failure) {
	tenant := e.storage.Tenant(actor)
	tv := int64(tenant)
	c, err := e.pool.Acquire(background)
	if err != nil {
		return outcome[Reply, Error]{}, &failure{failPool, err}
	}
	ended := false
	var f *failure
	defer func() { release(c, ended && f == nil) }()
	var out outcome[Reply, Error]
	out, f = e.readTransact(c, actor, cmd, tenant, tv)
	ended = true
	return out, f
}

func (e *Engine[Principal, Snapshot, Command, WriteSet, Reply, Error]) readTransact(
	c *pgxpool.Conn, actor Principal, cmd Command, tenant uint64, tv int64,
) (outcome[Reply, Error], *failure) {
	var out outcome[Reply, Error]
	if _, err := c.Exec(background, beginRead); err != nil {
		return out, lost(c, err)
	}
	rows, f := e.load(c, tv)
	if f != nil {
		return out, f
	}
	if f := e.fire(c, Loaded, tenant); f != nil {
		return out, f
	}
	d, f := e.decide(tv, rows, actor, cmd)
	if f != nil {
		return out, f
	}
	if d.refusal != nil {
		if _, err := c.Exec(background, rollback); err != nil {
			return out, lost(c, err)
		}
		out.refusal = d.refusal
		return out, nil
	}
	if len(d.statements) != 0 {
		if _, err := c.Exec(background, rollback); err != nil {
			return out, lost(c, err)
		}
		return out, broken("a read-only command wrote")
	}
	tag, err := c.Exec(background, commit)
	if err != nil {
		return out, lost(c, err)
	}
	if tag.String() != commit {
		return out, &failure{failPostgres, fmt.Errorf("COMMIT answered %s", tag)}
	}
	e.stats.commits.Add(1)
	out.reply = d.reply
	return out, nil
}

func role(name string) error {
	ok := len(name) > 0 && len(name) <= 63 && (name[0] == '_' || 'a' <= name[0] && name[0] <= 'z')
	for i := 1; ok && i < len(name); i++ {
		b := name[i]
		ok = b == '_' || 'a' <= b && b <= 'z' || '0' <= b && b <= '9'
	}
	if !ok {
		return fmt.Errorf("%w: the role name %q is not [a-z_][a-z0-9_]*", leanharbor.ErrBroken, name)
	}
	return nil
}

// Lockdown is run by an administrator of the database: it creates the tables and the
// framework's table, makes owner own them, and lets engineRole read and write their rows and
// nothing else: it cannot alter, drop or truncate them. owner is created without the right to
// log in if it does not exist. engineRole must exist and may not be a superuser; it gets USAGE
// and CREATE on the schema, so that the engine's CREATE TABLE IF NOT EXISTS at start finds the
// tables.
func Lockdown(tables []sql.Tab, adminURL, owner, engineRole string) error {
	if err := role(owner); err != nil {
		return err
	}
	if err := role(engineRole); err != nil {
		return err
	}
	if owner == engineRole {
		return fmt.Errorf("%w: the owner and the engine's role must differ", leanharbor.ErrBroken)
	}
	if !valid(tables) {
		return fmt.Errorf("%w: the tables are not valid", leanharbor.ErrBroken)
	}
	admin, err := pgx.Connect(background, adminURL)
	if err != nil {
		return database(err)
	}
	defer func() { _ = admin.Close(background) }()
	var super bool
	err = admin.QueryRow(background, "SELECT rolsuper FROM pg_roles WHERE rolname = $1", engineRole).Scan(&super)
	switch {
	case errors.Is(err, pgx.ErrNoRows):
		return fmt.Errorf("%w: the role %s does not exist", leanharbor.ErrBroken, engineRole)
	case err != nil:
		return database(err)
	case super:
		return fmt.Errorf("%w: the role %s is a superuser", leanharbor.ErrBroken, engineRole)
	}
	_, err = admin.Exec(background, fmt.Sprintf(
		"DO $$ BEGIN IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = '%s') "+
			"THEN CREATE ROLE \"%s\" NOLOGIN; END IF; END $$", owner, owner))
	if err != nil {
		return database(err)
	}
	var login bool
	err = admin.QueryRow(background, "SELECT rolcanlogin FROM pg_roles WHERE rolname = $1", owner).Scan(&login)
	if err != nil {
		return database(err)
	}
	if login {
		return fmt.Errorf("%w: the role %s can log in", leanharbor.ErrBroken, owner)
	}
	if err := create(admin, tables); err != nil {
		return database(err)
	}
	names := append([]string{}, frameworkTables...)
	for _, t := range tables {
		names = append(names, t.Name)
	}
	for _, name := range names {
		q, err := sql.Quote(name)
		if err != nil {
			return fmt.Errorf("%w: the table name %q does not quote", leanharbor.ErrBroken, name)
		}
		_, err = admin.Exec(background, fmt.Sprintf(
			"ALTER TABLE %s OWNER TO \"%s\"; REVOKE ALL ON %s FROM PUBLIC; "+
				"REVOKE ALL ON %s FROM \"%s\"; "+
				"GRANT SELECT, INSERT, UPDATE, DELETE ON %s TO \"%s\"",
			q, owner, q, q, engineRole, q, engineRole))
		if err != nil {
			return database(err)
		}
	}
	_, err = admin.Exec(background, fmt.Sprintf(
		"DO $$ BEGIN EXECUTE format('GRANT USAGE, CREATE ON SCHEMA %%I TO %%I', "+
			"current_schema(), '%s'); END $$", engineRole))
	if err != nil {
		return database(err)
	}
	return nil
}
