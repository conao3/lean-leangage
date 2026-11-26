package pg_test

// The engine's contract, item by item (the numbers of the list in pg.go), against the test
// process's PostgreSQL with injected faults: forced serialization failures and deadlocks,
// terminated backends, COMMITs lost before or after the server ran them, an HTTP client that
// stops waiting, other engines writing the same tenant, and many concurrent clients. Each test
// has a database of its own.

import (
	"errors"
	"fmt"
	"maps"
	"math"
	"net"
	"net/http/httptest"
	"strconv"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/jackc/pgx/v5"
	"github.com/jackc/pgx/v5/pgconn"

	"github.com/conao3/lean-leangage/go/leangage"
	"github.com/conao3/lean-leangage/go/leangage/httpformat"
	"github.com/conao3/lean-leangage/go/leangage/jsonlexemes"
	"github.com/conao3/lean-leangage/go/leangage/pg"
	"github.com/conao3/lean-leangage/go/leangage/pg/pgtest"
)

const inTime = 30 * time.Second

type result struct {
	reply   int64
	refusal *refused
	err     error
}

func key(k string, c cmd) *leangage.Idempotency {
	return &leangage.Idempotency{Scope: "u1", Key: k, Fingerprint: fmt.Appendf(nil, "%#v", c)}
}

// begin runs the command on a goroutine of its own.
func begin(e *engine, a actor, c cmd, idem *leangage.Idempotency) <-chan result {
	done := make(chan result, 1)
	go func() {
		reply, refusal, err := e.Execute(a, c, idem)
		done <- result{reply, refusal, err}
	}()
	return done
}

func wait(t *testing.T, done <-chan result, within time.Duration) result {
	t.Helper()
	select {
	case r := <-done:
		return r
	case <-time.After(within):
		t.Fatal("not in time")
		return result{}
	}
}

func execute(t *testing.T, e *engine, a actor, c cmd, idem *leangage.Idempotency) result {
	t.Helper()
	return wait(t, begin(e, a, c, idem), inTime)
}

func run(t *testing.T, e *engine, tenant uint64, c cmd) result {
	t.Helper()
	return execute(t, e, who(tenant), c, nil)
}

func runKeyed(t *testing.T, e *engine, tenant uint64, k string, c cmd) result {
	t.Helper()
	return execute(t, e, who(tenant), c, key(k, c))
}

// accepted is the reply of an accepted command.
func accepted(t *testing.T, r result) int64 {
	t.Helper()
	if r.err != nil || r.refusal != nil {
		t.Fatalf("not accepted: %+v", r)
	}
	return r.reply
}

func isRefused(t *testing.T, r result) {
	t.Helper()
	if r.err != nil || r.refusal == nil || *r.refusal != negative {
		t.Fatalf("not refused: %+v", r)
	}
}

func fails(t *testing.T, r result, want error) {
	t.Helper()
	if !errors.Is(r.err, want) {
		t.Fatalf("got %+v, want %v", r, want)
	}
}

func equal[T comparable](t *testing.T, got, want T, what string) {
	t.Helper()
	if got != want {
		t.Fatalf("%s: got %v, want %v", what, got, want)
	}
}

func hasCell(t *testing.T, d *db, tenant uint64, id, want int64) {
	t.Helper()
	got, ok := d.cell(tenant, id)
	if !ok || got != want {
		t.Fatalf("cell %d of tenant %d: got %d (stored %v), want %d", id, tenant, got, ok, want)
	}
}

func noCell(t *testing.T, d *db, tenant uint64, id int64) {
	t.Helper()
	if got, ok := d.cell(tenant, id); ok {
		t.Fatalf("cell %d of tenant %d: got %d, want no row", id, tenant, got)
	}
}

// conflict is an outside transaction that changes cell 0 of tenant after the attempt's
// snapshot, and advances the tenant's version as an engine's commit does.
func (d *db) conflict(tenant uint64) {
	d.exec("WITH u AS (UPDATE cells SET v = v + 100 WHERE tenant_id = $1 AND id = 0 RETURNING 1) "+
		"INSERT INTO leangage_version (tenant_id, version) SELECT $1, 1 FROM u "+
		"ON CONFLICT (tenant_id) DO UPDATE SET version = leangage_version.version + 1",
		int64(tenant))
}

// Items 1 and 2: one attempt is one SERIALIZABLE read-write transaction; a retry is a new
// transaction that reads the rows again and calls Transition again.
func TestSerializationFailuresRetryInANewTransaction(t *testing.T) {
	d := setup(t, "contract_ssi")
	hook, seen := hookAt(pg.Loaded, 2, func(a pg.Attempt) { d.conflict(a.Tenant) })
	plain := d.engine(1, pg.DefaultConfig())
	accepted(t, run(t, plain, 1, add{0, 5}))
	e := d.engine(2, config(20, true, hook))
	r := accepted(t, run(t, e, 1, add{0, 1}))
	equal(t, e.Stats().Attempts, 3, "attempts")
	equal(t, e.Stats().Retries, 2, "retries")
	// Each retry read the outside commits made after the snapshot of the attempt before it.
	equal(t, r, 5+100+100+1, "reply")
	hasCell(t, d, 1, 0, 206)
	txs := seen.at(pg.Loaded)
	equal(t, len(txs), 3, "attempts that loaded")
	for _, a := range txs {
		equal(t, a.Tx.Isolation, "serializable", "isolation")
		equal(t, a.Tx.ReadOnly, false, "read only")
	}
	if txs[0].Tx.Vxid == txs[1].Tx.Vxid || txs[1].Tx.Vxid == txs[2].Tx.Vxid {
		t.Fatalf("one transaction for two attempts: %+v %+v %+v", *txs[0].Tx, *txs[1].Tx, *txs[2].Tx)
	}
}

// Item 2: retries stop after MaxAttempts with ErrRetriesExhausted, and no attempt left a write
// or a stored reply.
func TestSerializationFailuresExhaustAfterMaxAttempts(t *testing.T) {
	d := setup(t, "contract_exhaust")
	hook, _ := hookAt(pg.Loaded, math.MaxUint64, func(a pg.Attempt) { d.conflict(a.Tenant) })
	plain := d.engine(1, pg.DefaultConfig())
	accepted(t, run(t, plain, 1, add{0, 5}))
	e := d.engine(2, config(3, true, hook))
	fails(t, runKeyed(t, e, 1, "k", add{0, 1}), leangage.ErrRetriesExhausted)
	equal(t, e.Stats().Attempts, 3, "attempts")
	hasCell(t, d, 1, 0, 305)
	equal(t, d.replies(1), 0, "replies")
}

// Item 2 (deadlock): the attempt holds the tenant's advisory lock and waits for a row an
// outside transaction holds, which then waits for the advisory lock. PostgreSQL aborts the
// attempt with 40P01 (the outside session waits 30 s before it checks), and the retry succeeds.
func TestDeadlocksAreRetried(t *testing.T) {
	d := setup(t, "contract_deadlock")
	other := pgtest.Connect(t, d.adminURL())
	outside := make(chan error, 1)
	hook, _ := hookAt(pg.Loaded, 1, func(a pg.Attempt) {
		_, err := other.Exec(ctx, fmt.Sprintf("BEGIN; SET LOCAL deadlock_timeout = '30s'; "+
			"UPDATE cells SET v = v WHERE tenant_id = %d AND id = 0", a.Tenant))
		if err != nil {
			outside <- err
			return
		}
		go func() {
			for {
				var n int64
				err := other.QueryRow(ctx, "SELECT count(*) FROM pg_locks WHERE pid = $1 AND NOT granted", a.Pid).Scan(&n)
				if err != nil {
					outside <- err
					return
				}
				if n > 0 {
					break
				}
				time.Sleep(5 * time.Millisecond)
			}
			if _, err := other.Exec(ctx, "SELECT pg_advisory_xact_lock($1)", int64(a.Tenant)); err != nil {
				outside <- err
				return
			}
			_, err := other.Exec(ctx, "ROLLBACK")
			outside <- err
		}()
	})
	e := d.engine(2, config(20, true, hook))
	plain := d.engine(1, pg.DefaultConfig())
	accepted(t, run(t, plain, 1, add{0, 5}))
	r := accepted(t, run(t, e, 1, add{0, 1}))
	if err := <-outside; err != nil {
		t.Fatal(err)
	}
	equal(t, e.Stats().Retries, 1, "one retry, after the deadlock")
	equal(t, r, 6, "reply")
	hasCell(t, d, 1, 0, 6)
	equal(t, d.noAdvisoryLocks(2*time.Second), 0, "advisory locks")
}

// Item 2 (lost connection): a backend terminated before COMMIT (at each point of an attempt)
// retries from BEGIN on a new connection, and the command takes effect once, with or without a
// key. Without a key, a connection lost right before COMMIT and noticed only by COMMIT is
// ErrCommitUnknown (it did not commit; the engine cannot know that).
func TestKilledBeforeCommitRetriesOnce(t *testing.T) {
	d := setup(t, "contract_kill")
	tenant := uint64(0)
	for _, point := range []pg.Point{pg.Locked, pg.Loaded, pg.Written} {
		for _, keyed := range []bool{false, true} {
			tenant++
			hook, seen := hookAt(point, 1, func(a pg.Attempt) { d.kill(a.Pid) })
			e := d.engine(2, config(20, true, hook))
			c := add{0, 7}
			var r result
			if keyed {
				r = runKeyed(t, e, tenant, "k", c)
			} else {
				r = run(t, e, tenant, c)
			}
			name := fmt.Sprintf("%v, keyed %v", point, keyed)
			stored := int64(0)
			if point == pg.Written && !keyed {
				fails(t, r, leangage.ErrCommitUnknown)
				noCell(t, d, tenant, 0)
			} else {
				equal(t, accepted(t, r), 7, name)
				hasCell(t, d, tenant, 0, 7)
				equal(t, e.Stats().Retries, 1, name+": one retry")
				attempts := seen.at(point)
				equal(t, len(attempts), 2, name)
				if attempts[0].Pid == attempts[1].Pid {
					t.Fatalf("%s: the retry ran on the same connection", name)
				}
				if keyed {
					stored = 1
				}
			}
			equal(t, d.replies(tenant), stored, name+": replies")
		}
	}
	equal(t, d.noAdvisoryLocks(2*time.Second), 0, "advisory locks")
}

// Item 3: a refused command rolls back and stores no row and no reply, with or without a key.
func TestRefusalsWriteNothing(t *testing.T) {
	d := setup(t, "contract_refusal")
	e := d.engine(2, pg.DefaultConfig())
	accepted(t, run(t, e, 1, add{0, 5}))
	before := e.Stats()
	isRefused(t, run(t, e, 1, add{0, -10}))
	isRefused(t, runKeyed(t, e, 1, "k", add{0, -10}))
	isRefused(t, run(t, e, 1, move{0, 1, 50}))
	equal(t, e.Stats().Commits, before.Commits, "no commit")
	if got := d.cells(1); !maps.Equal(got, map[int64]int64{0: 5}) {
		t.Fatalf("cells: %v", got)
	}
	equal(t, d.replies(1), 0, "replies")
	// The refusal stored no reply under its key: the same command runs again once it is
	// accepted.
	accepted(t, run(t, e, 1, add{0, 20}))
	equal(t, accepted(t, runKeyed(t, e, 1, "k", add{0, -10})), 15, "reply")
	equal(t, d.replies(1), 1, "replies")
}

// Item 4: the app's writes and the stored reply commit together. A COMMIT lost before the
// server ran it leaves neither; one lost after the server committed leaves both.
func TestRepliesCommitWithTheWrites(t *testing.T) {
	d := setup(t, "contract_atomic")
	p := startProxy(t)
	e := d.engineAt(p.url(d.name), 1, config(1, true, nil))
	p.arm(dropBefore)
	fails(t, runKeyed(t, e, 1, "a", add{0, 3}), leangage.ErrRetriesExhausted)
	noCell(t, d, 1, 0)
	equal(t, d.replies(1), 0, "replies")
	p.arm(dropAfter)
	fails(t, runKeyed(t, e, 2, "a", add{0, 3}), leangage.ErrRetriesExhausted)
	hasCell(t, d, 2, 0, 3)
	equal(t, d.replies(2), 1, "replies")
	equal(t, fmt.Sprint(p.seen()), fmt.Sprint([]outcome{notSent, committed}), "outcomes")
}

// Item 4: a reply is stored per tenant, scope and key; the same key with the same command
// replays it without running the command, and with another command is refused.
func TestIdempotencyKeysReplayAndConflict(t *testing.T) {
	d := setup(t, "contract_keys")
	e := d.engine(2, pg.DefaultConfig())
	equal(t, accepted(t, runKeyed(t, e, 1, "k", add{0, 2})), 2, "first")
	equal(t, accepted(t, runKeyed(t, e, 1, "k", add{0, 2})), 2, "replayed")
	equal(t, e.Stats().Replays, 1, "one replay")
	hasCell(t, d, 1, 0, 2)
	fails(t, runKeyed(t, e, 1, "k", add{0, 3}), leangage.ErrIdempotencyConflict)
	otherScope := &leangage.Idempotency{Scope: "u2", Key: "k", Fingerprint: fmt.Appendf(nil, "%#v", add{0, 2})}
	equal(t, accepted(t, execute(t, e, who(1), add{0, 2}, otherScope)), 4, "another scope runs the command")
	equal(t, accepted(t, runKeyed(t, e, 2, "k", add{0, 3})), 3, "another tenant")
	hasCell(t, d, 1, 0, 4)
	equal(t, d.replies(1), 2, "replies")
}

// Item 4: concurrent requests with one key run the command once; the others replay its reply
// (a loser of the race for the key's row gets 23505 and retries).
func TestConcurrentRequestsWithOneKeyRunOnce(t *testing.T) {
	d := setup(t, "contract_one_key")
	for _, c := range []struct {
		tenant uint64
		lock   bool
	}{{1, true}, {2, false}} {
		e := d.engine(8, config(20, c.lock, nil))
		requests := []<-chan result{}
		for range 32 {
			requests = append(requests, begin(e, who(c.tenant), add{0, 1}, key("once", add{0, 1})))
		}
		for _, r := range requests {
			equal(t, accepted(t, wait(t, r, inTime)), 1, fmt.Sprintf("lock %v", c.lock))
		}
		hasCell(t, d, c.tenant, 0, 1)
		equal(t, d.replies(c.tenant), 1, "replies")
		equal(t, e.Stats().Commits, 1, "one commit")
		equal(t, e.Stats().Replays, 31, "31 replays")
	}
}

// Item 5: the tenant's advisory lock is held from before BEGIN to before the connection returns
// to the pool. A request queued behind it waits in pg_advisory_lock before its transaction, so
// it reads the first request's commit and commits without a retry.
func TestAdvisoryLockIsHeldAroundTheTransaction(t *testing.T) {
	d := setup(t, "contract_lock")
	release := make(chan struct{})
	held := make(chan int64, 1)
	hook, _ := hookAt(pg.Written, 1, func(a pg.Attempt) {
		var n int64
		d.query("SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND granted "+
			"AND pid = $1 AND objid = $2", []any{a.Pid, uint32(a.Tenant)}, &n)
		held <- n
		<-release
	})
	e := d.engine(2, config(20, true, hook))
	free := sync.OnceFunc(func() { close(release) })
	// Before the engine's cleanup, which waits for the connection the hook holds.
	t.Cleanup(free)
	first := begin(e, who(1), add{0, 1}, nil)
	equal(t, <-held, 1, "the lock is held before COMMIT")
	second := begin(e, who(1), add{0, 10}, nil)
	var waiting int32
	deadline := time.Now().Add(10 * time.Second)
	for {
		d.mu.Lock()
		err := d.admin.QueryRow(ctx, "SELECT l.pid FROM pg_locks l JOIN pg_stat_activity a ON a.pid = l.pid "+
			"WHERE l.locktype = 'advisory' AND NOT l.granted AND a.query = $1 "+
			"AND a.datname = current_database()", "SELECT pg_advisory_lock($1)").Scan(&waiting)
		d.mu.Unlock()
		if err == nil {
			break
		}
		if !errors.Is(err, pgx.ErrNoRows) {
			t.Fatal(err)
		}
		if time.Now().After(deadline) {
			t.Fatal("the second request does not wait for the lock")
		}
		time.Sleep(5 * time.Millisecond)
	}
	// The waiting request has not read the table: it holds no lock on it, not even the
	// predicate lock of a SERIALIZABLE read.
	var read int64
	d.query("SELECT count(*) FROM pg_locks WHERE pid = $1 AND relation = 'cells'::regclass", []any{waiting}, &read)
	equal(t, read, 0, "locks on the table")
	free()
	equal(t, accepted(t, wait(t, first, inTime)), 1, "first")
	equal(t, accepted(t, wait(t, second, inTime)), 11, "it read the first commit")
	equal(t, e.Stats().Retries, 0, "no retry")
	equal(t, d.noAdvisoryLocks(2*time.Second), 0, "advisory locks")
}

// cellsApi serves add commands of cells over HTTP: `{"cell": c, "delta": d}`.
type cellsApi struct{}

func (cellsApi) Request(tenant, user, _, _ uint64, body httpformat.Body) (actor, cmd, *httpformat.Response) {
	read, ok := body.(httpformat.BodyJson)
	if !ok {
		return actor{}, nil, &httpformat.Response{Status: 400}
	}
	lexemes, _ := unpacked(read.Packed)
	if len(lexemes) != 6 {
		return actor{}, nil, &httpformat.Response{Status: 400}
	}
	number := func(i int) int64 {
		text, _ := lexemes[i].(jsonlexemes.LexemeNumber)
		n, _ := strconv.ParseInt(text.Text, 10, 64)
		return n
	}
	return actor{tenant, user}, add{number(2), number(4)}, nil
}

func (cellsApi) Respond(r int64, refusal *refused) httpformat.Response {
	if refusal != nil {
		return httpformat.Response{Status: 422, Body: []byte(`{"error":"negative"}`)}
	}
	return httpformat.Response{Status: 200, Body: strconv.AppendInt(nil, r, 10)}
}

func (cellsApi) Fingerprint(c cmd) []byte { return fmt.Appendf(nil, "%#v", c) }

func (cellsApi) Scope(a actor) string { return fmt.Sprintf("u%d", a.user) }

// Item 5: no advisory lock is left after a commit, a refusal, an attempt whose backend was
// terminated, a failed request, or an HTTP client that closed its connection while its request
// held the lock; the pool keeps its connections and another engine gets the tenant at once.
func TestAdvisoryLocksAreReleased(t *testing.T) {
	d := setup(t, "contract_release")
	hook, _ := hookAt(pg.Loaded, 1, func(a pg.Attempt) { d.kill(a.Pid) })
	e := d.engine(2, config(20, true, hook))
	accepted(t, run(t, e, 1, add{0, 5}))
	equal(t, d.noAdvisoryLocks(2*time.Second), 0, "killed")
	accepted(t, run(t, e, 1, add{0, 1}))
	equal(t, d.advisoryLocks(), 0, "commit")
	isRefused(t, run(t, e, 1, add{0, -100}))
	equal(t, d.advisoryLocks(), 0, "refusal")
	accepted(t, runKeyed(t, e, 1, "k", add{0, 1}))
	fails(t, runKeyed(t, e, 1, "k", add{0, 2}), leangage.ErrIdempotencyConflict)
	equal(t, d.advisoryLocks(), 0, "failed request")

	release := make(chan struct{})
	written := make(chan struct{})
	hook, _ = hookAt(pg.Written, 1, func(pg.Attempt) {
		close(written)
		<-release
	})
	blocked := d.engine(2, config(20, true, hook))
	free := sync.OnceFunc(func() { close(release) })
	t.Cleanup(free)
	secret := []byte("secret")
	server := httptest.NewServer(leangage.RpcHandler(blocked, cellsApi{}, secret))
	token := leangage.Issue(secret, leangage.Claims{Tenant: 1, User: 1, Expiry: 1 << 62})
	client, err := net.Dial("tcp", server.Listener.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	body := `{"cell":0,"delta":100}`
	fmt.Fprintf(client, "POST /rpc HTTP/1.1\r\nHost: x\r\nAuthorization: Bearer %s\r\n"+
		"Content-Length: %d\r\n\r\n%s", token, len(body), body)
	<-written
	// The client stops waiting while its request holds the tenant's lock.
	_ = client.Close()
	free()
	// Close waits for the request, which ran to its end: its command committed once.
	server.Close()
	equal(t, d.noAdvisoryLocks(5*time.Second), 0, "the client closed its connection")
	hasCell(t, d, 1, 0, 107)
	other := d.engine(1, config(1, true, nil))
	equal(t, accepted(t, wait(t, begin(other, who(1), add{0, 1}, nil), 2*time.Second)), 108, "the tenant is free")
	equal(t, blocked.Idle(), 1, "the connection is back in the pool")
}

// Item 6: a read-only command runs in one SERIALIZABLE READ ONLY DEFERRABLE transaction
// without the advisory lock, is retried after a lost connection, and fails if it writes; with
// a key it takes the write path.
func TestReadOnlyPath(t *testing.T) {
	d := setup(t, "contract_read")
	var mu sync.Mutex
	locks := []int64{}
	hook, seen := hookAt(pg.Loaded, math.MaxUint64, func(a pg.Attempt) {
		var n int64
		d.query("SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND pid = $1", []any{a.Pid}, &n)
		mu.Lock()
		locks = append(locks, n)
		mu.Unlock()
	})
	e := d.engine(2, config(20, true, hook))
	accepted(t, run(t, e, 1, add{0, 5}))
	before := e.Stats()
	equal(t, accepted(t, run(t, e, 1, get{0})), 5, "get")
	equal(t, e.Stats().Reads-before.Reads, 1, "one read")
	loaded := seen.at(pg.Loaded)
	read := loaded[len(loaded)-1].Tx
	equal(t, read.Isolation, "serializable", "isolation")
	if !read.ReadOnly || !read.Deferrable {
		t.Fatalf("not read only and deferrable: %+v", *read)
	}
	mu.Lock()
	equal(t, locks[len(locks)-1], 0, "no advisory lock")
	mu.Unlock()
	equal(t, len(seen.at(pg.Locked)), 1, "only the write took the lock")

	// A command that claims to read only and writes fails, and nothing is stored.
	fails(t, run(t, e, 1, poke{0}), leangage.ErrBroken)
	hasCell(t, d, 1, 0, 5)

	// With a key, a read takes the write path and stores its reply.
	before = e.Stats()
	equal(t, accepted(t, runKeyed(t, e, 1, "r", get{0})), 5, "keyed get")
	equal(t, e.Stats().Reads, before.Reads, "not a read")
	loaded = seen.at(pg.Loaded)
	equal(t, loaded[len(loaded)-1].Tx.ReadOnly, false, "read only")
	equal(t, d.replies(1), 1, "replies")

	// A lost connection is retried.
	hook, seen = hookAt(pg.Loaded, 1, func(a pg.Attempt) { d.kill(a.Pid) })
	killed := d.engine(2, config(20, true, hook))
	equal(t, accepted(t, run(t, killed, 1, get{0})), 5, "get")
	equal(t, killed.Stats().Reads, 2, "two reads")
	equal(t, len(seen.at(pg.Loaded)), 2, "attempts that loaded")
}

// Item 7: without a key, a COMMIT lost before or after the server ran it is ErrCommitUnknown,
// not retried; the first did not commit and the second did.
func TestLostCommitWithoutKeyIsUnknown(t *testing.T) {
	d := setup(t, "contract_unknown")
	p := startProxy(t)
	e := d.engineAt(p.url(d.name), 1, config(20, true, nil))
	p.arm(dropBefore)
	fails(t, run(t, e, 1, add{0, 3}), leangage.ErrCommitUnknown)
	p.arm(dropAfter)
	fails(t, run(t, e, 2, add{0, 3}), leangage.ErrCommitUnknown)
	equal(t, e.Stats().Retries, 0, "not retried")
	noCell(t, d, 1, 0)
	hasCell(t, d, 2, 0, 3)
	equal(t, fmt.Sprint(p.seen()), fmt.Sprint([]outcome{notSent, committed}), "outcomes")
}

// Item 7, with a key: a lost COMMIT is retried, and the command takes effect once; after a
// COMMIT the server ran, the retry replays the stored reply.
func TestLostCommitWithKeyRunsOnce(t *testing.T) {
	d := setup(t, "contract_lost_keyed")
	p := startProxy(t)
	e := d.engineAt(p.url(d.name), 1, config(20, true, nil))
	p.arm(dropBefore)
	equal(t, accepted(t, runKeyed(t, e, 1, "k", add{0, 3})), 3, "dropped before")
	p.arm(dropAfter)
	equal(t, accepted(t, runKeyed(t, e, 2, "k", add{0, 3})), 3, "dropped after")
	hasCell(t, d, 1, 0, 3)
	hasCell(t, d, 2, 0, 3)
	equal(t, e.Stats().Replays, 1, "the second replayed")
	equal(t, fmt.Sprint(p.seen()), fmt.Sprint([]outcome{notSent, committed}), "outcomes")
}

// With PostgreSQL's SERIALIZABLE, whose commits equal a serial order: 64 clients move units
// between four cells of one tenant, with and without the advisory lock. The total is kept, and
// each cell holds what the accepted moves left there.
func TestConcurrentMovesAreSerial(t *testing.T) {
	d := setup(t, "contract_serial")
	for _, c := range []struct {
		tenant uint64
		lock   bool
	}{{1, true}, {2, false}} {
		e := d.engine(8, config(1000, c.lock, nil))
		for cell := range int64(4) {
			accepted(t, run(t, e, c.tenant, add{cell, 100}))
		}
		moved := make(chan [][2]int64, 64)
		for client := range int64(64) {
			go func() {
				out := [][2]int64{}
				for i := range int64(8) {
					from, to := (client+i)%4, (client+i+1)%4
					if _, refusal, err := e.Execute(who(c.tenant), move{from, to, 1}, nil); err == nil && refusal == nil {
						out = append(out, [2]int64{from, to})
					}
				}
				moved <- out
			}()
		}
		expected := map[int64]int64{0: 100, 1: 100, 2: 100, 3: 100}
		accepted := 0
		for range 64 {
			for _, m := range <-moved {
				expected[m[0]]--
				expected[m[1]]++
				accepted++
			}
		}
		equal(t, accepted, 512, fmt.Sprintf("lock %v", c.lock))
		if got := d.cells(c.tenant); !maps.Equal(got, expected) {
			t.Fatalf("lock %v: cells %v, want %v", c.lock, got, expected)
		}
		if c.lock {
			equal(t, e.Stats().Retries, 0, "the lock spares every retry")
		}
	}
}

// The role split: the tables belong to a role that cannot log in, and the engine's role reads
// and writes their rows but cannot alter, drop or truncate them. Lockdown refuses a superuser
// and can run again; the engine starts on the tables it made.
func TestRolesKeepTheEngineToRows(t *testing.T) {
	d := setup(t, "contract_roles")
	var owner string
	d.query("SELECT tableowner FROM pg_tables WHERE tablename = 'cells'", nil, &owner)
	equal(t, owner, pgtest.Owner, "owner")
	conn := pgtest.Connect(t, d.url)
	for _, statement := range []string{
		"DROP TABLE cells",
		"TRUNCATE cells",
		"ALTER TABLE cells ADD COLUMN x BIGINT",
		"DROP TABLE leangage_idempotency",
		"DROP TABLE leangage_version",
		"TRUNCATE leangage_version",
	} {
		_, err := conn.Exec(ctx, statement)
		var pgErr *pgconn.PgError
		if !errors.As(err, &pgErr) || pgErr.Code != "42501" {
			t.Fatalf("%s: %v", statement, err)
		}
	}
	e := d.engine(1, pg.DefaultConfig())
	equal(t, accepted(t, run(t, e, 1, add{0, 1})), 1, "reply")
	tables := cells{}.Tables()
	if err := pg.Lockdown(tables, d.adminURL(), pgtest.Owner, pgtest.EngineRole); err != nil {
		t.Fatalf("lockdown runs again: %v", err)
	}
	if err := pg.Lockdown(tables, d.adminURL(), pgtest.Owner, "postgres"); !errors.Is(err, leangage.ErrBroken) {
		t.Fatalf("a superuser: %v", err)
	}
	if err := pg.Lockdown(tables, d.adminURL(), pgtest.EngineRole, pgtest.Owner); !errors.Is(err, leangage.ErrBroken) {
		t.Fatalf("an owner that can log in: %v", err)
	}
	hasCell(t, d, 1, 0, 1)
}

// Item 8: an engine reads the rows another engine wrote, whichever path it takes, and reads no
// row while the version is the one it remembers.
func TestOtherEnginesWritesAreRead(t *testing.T) {
	d := setup(t, "contract_other")
	a := d.engine(2, pg.DefaultConfig())
	b := d.engine(2, pg.DefaultConfig())
	equal(t, accepted(t, run(t, a, 1, add{0, 5})), 5, "add")
	equal(t, a.Stats().Loads, 1, "loads")
	equal(t, accepted(t, run(t, a, 1, get{0})), 5, "get")
	equal(t, accepted(t, run(t, a, 1, add{0, 1})), 6, "add")
	equal(t, a.Stats().Loads, 1, "the remembered snapshot, on both paths")
	equal(t, accepted(t, run(t, b, 1, add{0, 10})), 16, "the other engine")
	equal(t, accepted(t, run(t, a, 1, get{0})), 16, "the read-only path")
	equal(t, a.Stats().Loads, 2, "loads")
	equal(t, accepted(t, run(t, b, 1, move{0, 1, 6})), 10, "move")
	equal(t, accepted(t, run(t, a, 1, add{1, 1})), 7, "the write path")
	equal(t, accepted(t, runKeyed(t, b, 1, "k", get{0})), 10, "keyed")
	equal(t, accepted(t, run(t, b, 1, get{1})), 7, "get")
	equal(t, a.Stats().Loads, 3, "loads")
	equal(t, b.Stats().Loads, 2, "its own commit remembered")
	if got := d.cells(1); !maps.Equal(got, map[int64]int64{0: 10, 1: 7}) {
		t.Fatalf("cells %v", got)
	}
}

const advanceVersion = "INSERT INTO leangage_version (tenant_id, version) VALUES ($1, 1) " +
	"ON CONFLICT (tenant_id) DO UPDATE SET version = leangage_version.version + 1 " +
	"RETURNING version"

// Item 8, on PostgreSQL's side: two transactions that read a tenant's version and advance it
// cannot both commit, whether the row exists or not. The second fails with 40001, which the
// engines retry, and not with 23505.
func TestVersionRowsConflict(t *testing.T) {
	d := setup(t, "contract_version")
	e := d.engine(1, pg.DefaultConfig())
	accepted(t, run(t, e, 2, add{0, 1}))
	for _, c := range []struct{ tenant, before int64 }{{1, 0}, {2, 1}} {
		first, second := pgtest.Connect(t, d.url), pgtest.Connect(t, d.url)
		for _, conn := range []*pgx.Conn{first, second} {
			if _, err := conn.Exec(ctx, "BEGIN ISOLATION LEVEL SERIALIZABLE"); err != nil {
				t.Fatal(err)
			}
			var read int64
			err := conn.QueryRow(ctx, "SELECT version FROM leangage_version WHERE tenant_id = $1", c.tenant).Scan(&read)
			if err != nil && !errors.Is(err, pgx.ErrNoRows) {
				t.Fatal(err)
			}
			equal(t, read, c.before, "the version read")
		}
		var advanced int64
		if err := first.QueryRow(ctx, advanceVersion, c.tenant).Scan(&advanced); err != nil {
			t.Fatal(err)
		}
		equal(t, advanced, c.before+1, "advanced")
		done := make(chan error, 1)
		go func() {
			var v int64
			done <- second.QueryRow(ctx, advanceVersion, c.tenant).Scan(&v)
		}()
		select {
		case err := <-done:
			t.Fatalf("tenant %d: the second did not wait for the first: %v", c.tenant, err)
		case <-time.After(200 * time.Millisecond):
		}
		if _, err := first.Exec(ctx, "COMMIT"); err != nil {
			t.Fatal(err)
		}
		var pgErr *pgconn.PgError
		if err := <-done; !errors.As(err, &pgErr) || pgErr.Code != "40001" {
			t.Fatalf("tenant %d: %v", c.tenant, err)
		}
		if _, err := second.Exec(ctx, "ROLLBACK"); err != nil {
			t.Fatal(err)
		}
	}
}

// Item 8: a COMMIT of unknown outcome forgets the tenant's snapshot. The engine reads the rows
// again, whether the COMMIT ran or not, and after another engine's commit.
func TestLostCommitForgetsTheSnapshot(t *testing.T) {
	d := setup(t, "contract_forget")
	p := startProxy(t)
	e := d.engineAt(p.url(d.name), 1, config(20, true, nil))
	other := d.engine(1, pg.DefaultConfig())
	equal(t, accepted(t, run(t, e, 1, add{0, 5})), 5, "add")
	p.arm(dropBefore)
	fails(t, run(t, e, 1, add{0, 1}), leangage.ErrCommitUnknown)
	equal(t, accepted(t, run(t, e, 1, get{0})), 5, "not committed")
	equal(t, accepted(t, run(t, other, 1, add{0, 10})), 15, "the other engine")
	equal(t, accepted(t, run(t, e, 1, get{0})), 15, "the other engine's commit")
	p.arm(dropAfter)
	fails(t, run(t, e, 1, add{0, 1}), leangage.ErrCommitUnknown)
	equal(t, accepted(t, run(t, e, 1, add{0, 1})), 17, "committed")
	equal(t, accepted(t, run(t, other, 1, get{0})), 17, "the other engine reads it")
	equal(t, e.Stats().Loads, 4, "every attempt after a lost COMMIT reads the rows")
	equal(t, fmt.Sprint(p.seen()), fmt.Sprint([]outcome{notSent, committed}), "outcomes")
}

// Item 8: a refusal, and an attempt rolled back by a terminated backend, leave the remembered
// snapshot as the last commit left it: the refusal reads no row, and the retry runs the command
// on what was committed.
func TestRefusalsAndRollbacksKeepTheSnapshot(t *testing.T) {
	d := setup(t, "contract_keep")
	var armed atomic.Bool
	hook, _ := hookAt(pg.Written, math.MaxUint64, func(a pg.Attempt) {
		if armed.Swap(false) {
			d.kill(a.Pid)
		}
	})
	e := d.engine(2, config(20, true, hook))
	equal(t, accepted(t, run(t, e, 1, add{0, 5})), 5, "add")
	isRefused(t, run(t, e, 1, add{0, -6}))
	isRefused(t, runKeyed(t, e, 1, "k", add{0, -6}))
	equal(t, accepted(t, run(t, e, 1, get{0})), 5, "get")
	equal(t, accepted(t, run(t, e, 1, add{0, 1})), 6, "add")
	equal(t, e.Stats().Loads, 1, "one read of the rows")
	fresh := d.engine(2, pg.DefaultConfig())
	isRefused(t, run(t, fresh, 1, add{0, -7}))
	equal(t, accepted(t, run(t, fresh, 1, get{0})), 6, "get")
	equal(t, fresh.Stats().Loads, 1, "the snapshot loaded for a refusal")
	before := e.Stats().Loads
	equal(t, accepted(t, run(t, e, 2, add{0, 3})), 3, "add")
	armed.Store(true)
	fails(t, run(t, e, 2, add{0, 4}), leangage.ErrCommitUnknown)
	equal(t, accepted(t, run(t, e, 2, add{0, 4})), 7, "on the committed rows")
	hasCell(t, d, 2, 0, 7)
	equal(t, accepted(t, run(t, e, 3, add{0, 3})), 3, "add")
	armed.Store(true)
	equal(t, accepted(t, runKeyed(t, e, 3, "k", add{0, 4})), 7, "retried")
	hasCell(t, d, 3, 0, 7)
	equal(t, e.Stats().Loads-before, 4, "loads")
}

// Item 8: the engine remembers at most CacheTenants tenants and forgets the one it used least
// recently; with 0 it remembers none.
func TestRemembersAtMostCacheTenants(t *testing.T) {
	d := setup(t, "contract_capacity")
	two := pg.DefaultConfig()
	two.CacheTenants = 2
	e := d.engine(1, two)
	for tenant := range uint64(3) {
		accepted(t, run(t, e, tenant+1, add{0, 1}))
	}
	equal(t, e.Cached(), 2, "cached")
	equal(t, e.Stats().Loads, 3, "loads")
	equal(t, accepted(t, run(t, e, 2, get{0})), 1, "get")
	equal(t, e.Stats().Loads, 3, "tenant 2 remembered")
	equal(t, accepted(t, run(t, e, 1, get{0})), 1, "get")
	equal(t, e.Stats().Loads, 4, "tenant 1 forgotten")
	equal(t, accepted(t, run(t, e, 2, get{0})), 1, "get")
	equal(t, accepted(t, run(t, e, 1, get{0})), 1, "get")
	equal(t, e.Stats().Loads, 4, "tenants 1 and 2 remembered")
	equal(t, accepted(t, run(t, e, 3, get{0})), 1, "get")
	equal(t, e.Stats().Loads, 5, "tenant 3 forgotten")
	equal(t, e.Cached(), 2, "cached")
	none := pg.DefaultConfig()
	none.CacheTenants = 0
	e = d.engine(1, none)
	for range 3 {
		accepted(t, run(t, e, 1, add{0, 1}))
		accepted(t, run(t, e, 1, get{0}))
	}
	equal(t, e.Cached(), 0, "cached")
	equal(t, e.Stats().Loads, 6, "loads")
}

// Item 8 with SERIALIZABLE: two engines, each with 32 goroutines, move units between four cells
// of one tenant, with and without the advisory lock. Every cell holds what the accepted moves
// left, and both engines then read it.
func TestConcurrentEnginesAreSerial(t *testing.T) {
	d := setup(t, "contract_engines")
	for _, c := range []struct {
		tenant uint64
		lock   bool
	}{{1, true}, {2, false}} {
		engines := []*engine{d.engine(4, config(1000, c.lock, nil)), d.engine(4, config(1000, c.lock, nil))}
		for cell := range int64(4) {
			accepted(t, run(t, engines[0], c.tenant, add{cell, 100}))
		}
		moved := make(chan [][2]int64, 64)
		for client := range int64(64) {
			e := engines[client%2]
			go func() {
				out := [][2]int64{}
				for i := range int64(8) {
					from, to := (client+i)%4, (client+i+1)%4
					if _, refusal, err := e.Execute(who(c.tenant), move{from, to, 1}, nil); err == nil && refusal == nil {
						out = append(out, [2]int64{from, to})
					}
					_, _, _ = e.Execute(who(c.tenant), get{from}, nil)
				}
				moved <- out
			}()
		}
		expected := map[int64]int64{0: 100, 1: 100, 2: 100, 3: 100}
		accepted := 0
		for range 64 {
			for _, m := range <-moved {
				expected[m[0]]--
				expected[m[1]]++
				accepted++
			}
		}
		equal(t, accepted, 512, fmt.Sprintf("lock %v", c.lock))
		if got := d.cells(c.tenant); !maps.Equal(got, expected) {
			t.Fatalf("lock %v: cells %v, want %v", c.lock, got, expected)
		}
		for _, e := range engines {
			for cell, v := range expected {
				r := run(t, e, c.tenant, get{cell})
				if r.err != nil || r.refusal != nil || r.reply != v {
					t.Fatalf("lock %v: cell %d: %+v, want %d", c.lock, cell, r, v)
				}
			}
		}
	}
}

// unpacked is the tokens of a packed text, one by one.
func unpacked(packed string) ([]jsonlexemes.Lexeme, error) {
	lexemes, err := jsonlexemes.Unpack(packed)
	if err != nil || lexemes == nil {
		return nil, err
	}
	return *lexemes, nil
}
