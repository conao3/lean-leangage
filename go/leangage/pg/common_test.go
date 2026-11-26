package pg_test

// A small kernel written in Go for the engine's tests, a proxy that loses a COMMIT, and the
// queries a test makes as the server's superuser.

import (
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"math/big"
	"net"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"github.com/jackc/pgx/v5"

	"github.com/conao3/leanfran-go"

	"github.com/conao3/lean-leangage/go/leangage"
	"github.com/conao3/lean-leangage/go/leangage/pg"
	"github.com/conao3/lean-leangage/go/leangage/pg/pgtest"
	"github.com/conao3/lean-leangage/go/leangage/sql"
)

var ctx = context.Background()

type actor struct{ tenant, user uint64 }

// cmd is a command of cells. poke claims to read only and writes.
type cmd interface{ isCmd() }

type add struct{ cell, delta int64 }
type move struct{ from, to, amount int64 }
type get struct{ cell int64 }
type poke struct{ cell int64 }

func (add) isCmd()  {}
func (move) isCmd() {}
func (get) isCmd()  {}
func (poke) isCmd() {}

type refused int

const negative refused = 0

type snapshot = map[int64]int64
type writes = [][2]int64

// cells are numbered cells of integers per tenant.
type cells struct{}

type kernel = leangage.Kernel[actor, snapshot, cmd, writes, int64, refused]
type engine = pg.Engine[actor, snapshot, cmd, writes, int64, refused]

func (cells) Init() snapshot { return snapshot{} }

func (cells) Tenant(a actor) uint64 { return a.tenant }

func (cells) Transition(_ actor, snap snapshot, c cmd) (writes, int64, *refused) {
	refuse := negative
	switch c := c.(type) {
	case add:
		v := snap[c.cell] + c.delta
		if v < 0 {
			return nil, 0, &refuse
		}
		return writes{{c.cell, v}}, v, nil
	case move:
		f := snap[c.from] - c.amount
		if f < 0 {
			return nil, 0, &refuse
		}
		return writes{{c.from, f}, {c.to, snap[c.to] + c.amount}}, f, nil
	case get:
		return nil, snap[c.cell], nil
	case poke:
		return writes{{c.cell, snap[c.cell] + 1}}, snap[c.cell] + 1, nil
	}
	panic("unknown command")
}

func (cells) Apply(snap snapshot, ws writes) snapshot {
	for _, w := range ws {
		snap[w[0]] = w[1]
	}
	return snap
}

func (cells) Release(snapshot) {}

func (k cells) Scoped(_ *leanfran.Region, run func(kernel)) { run(k) }

func (cells) ReadOnly(c cmd) bool {
	switch c.(type) {
	case get, poke:
		return true
	}
	return false
}

func (cells) Tables() []sql.Tab {
	return []sql.Tab{{
		Name: "cells",
		Cols: []sql.Col{
			{Name: "id", Kind: sql.KindInt(), Nullable: false},
			{Name: "v", Kind: sql.KindInt(), Nullable: false},
		},
		Kl: big.NewInt(1),
	}}
}

func (cells) Load(rows [][][]sql.Val) (snapshot, bool) {
	if len(rows) != 1 {
		return nil, false
	}
	snap := snapshot{}
	for _, row := range rows[0] {
		if len(row) != 2 {
			return nil, false
		}
		id, ok1 := row[0].(sql.ValInt)
		v, ok2 := row[1].(sql.ValInt)
		if !ok1 || !ok2 {
			return nil, false
		}
		snap[id.V] = v.V
	}
	return snap, true
}

func (cells) Writes(ws writes) []sql.Write {
	out := []sql.Write{}
	for _, w := range ws {
		out = append(out, sql.WritePut{
			Table:  big.NewInt(0),
			KeyLen: big.NewInt(1),
			Row:    []sql.Val{sql.ValInt{V: w[0]}, sql.ValInt{V: w[1]}},
		})
	}
	return out
}

func (cells) EncodeStoredReply(r int64) []byte {
	return binary.BigEndian.AppendUint64(nil, uint64(r))
}

func (cells) DecodeStoredReply(b []byte) (int64, bool) {
	if len(b) != 8 {
		return 0, false
	}
	return int64(binary.BigEndian.Uint64(b)), true
}

func who(tenant uint64) actor { return actor{tenant, 1} }

// db is one database of the test process's server, with the tables of cells made by Lockdown.
type db struct {
	t    *testing.T
	name string
	// url is the engine role's connection string.
	url   string
	admin *pgx.Conn
	mu    sync.Mutex
}

func setup(t *testing.T, name string) *db {
	t.Parallel()
	c := pgtest.Start(t)
	url := c.Locked(t, cells{}.Tables(), name)
	return &db{t: t, name: name, url: url, admin: pgtest.Connect(t, c.AdminURL(name))}
}

func (d *db) adminURL() string { return pgtest.Start(d.t).AdminURL(d.name) }

func (d *db) engine(size int, config pg.Config) *engine {
	return d.engineAt(d.url, size, config)
}

func (d *db) engineAt(url string, size int, config pg.Config) *engine {
	d.t.Helper()
	e, err := pg.Connect(cells{}, url, size, config)
	if err != nil {
		d.t.Fatalf("the engine connects: %v", err)
	}
	d.t.Cleanup(e.Close)
	return e
}

// must fails the test on err. The hooks call it on the goroutine of an attempt, where the
// panic fails the request.
func (d *db) must(err error, what string) {
	if err != nil {
		d.t.Errorf("%s: %v", what, err)
		panic(err)
	}
}

// query runs a query on the admin connection, which the hooks share with the test.
func (d *db) query(sql string, args []any, dest ...any) {
	d.mu.Lock()
	defer d.mu.Unlock()
	d.must(d.admin.QueryRow(ctx, sql, args...).Scan(dest...), sql)
}

func (d *db) exec(sql string, args ...any) {
	d.mu.Lock()
	defer d.mu.Unlock()
	_, err := d.admin.Exec(ctx, sql, args...)
	d.must(err, sql)
}

func (d *db) cells(tenant uint64) map[int64]int64 {
	d.t.Helper()
	d.mu.Lock()
	defer d.mu.Unlock()
	rows, err := d.admin.Query(ctx, "SELECT id, v FROM cells WHERE tenant_id = $1", int64(tenant))
	if err != nil {
		d.t.Fatal(err)
	}
	out := map[int64]int64{}
	for rows.Next() {
		var id, v int64
		if err := rows.Scan(&id, &v); err != nil {
			d.t.Fatal(err)
		}
		out[id] = v
	}
	if err := rows.Err(); err != nil {
		d.t.Fatal(err)
	}
	return out
}

// cell is the value of the cell, and false when it has no row.
func (d *db) cell(tenant uint64, id int64) (int64, bool) {
	v, ok := d.cells(tenant)[id]
	return v, ok
}

func (d *db) replies(tenant uint64) int64 {
	var n int64
	d.query("SELECT count(*) FROM leangage_idempotency WHERE tenant_id = $1", []any{int64(tenant)}, &n)
	return n
}

// advisoryLocks are the advisory locks in this database held or awaited by any session but
// the admin's.
func (d *db) advisoryLocks() int64 {
	var n int64
	d.query("SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND pid <> pg_backend_pid() "+
		"AND database = (SELECT oid FROM pg_database WHERE datname = current_database())", nil, &n)
	return n
}

// noAdvisoryLocks waits until no session but the admin's holds an advisory lock; the number
// left.
func (d *db) noAdvisoryLocks(within time.Duration) int64 {
	start := time.Now()
	for {
		n := d.advisoryLocks()
		if n == 0 || time.Since(start) > within {
			return n
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// kill terminates the backend and waits until it is gone.
func (d *db) kill(pid int32) {
	var ok bool
	d.query("SELECT pg_terminate_backend($1)", []any{pid}, &ok)
	if !ok {
		d.must(fmt.Errorf("backend %d not terminated", pid), "kill")
	}
	for range 500 {
		var n int64
		d.query("SELECT count(*) FROM pg_stat_activity WHERE pid = $1", []any{pid}, &n)
		if n == 0 {
			return
		}
		time.Sleep(10 * time.Millisecond)
	}
	d.must(fmt.Errorf("backend %d still runs", pid), "kill")
}

// recorder records every attempt a hook sees.
type recorder struct {
	mu    sync.Mutex
	seen  []pg.Attempt
	fired atomic.Uint64
}

// hookAt is a hook that runs f at point for the first times attempts that reach it, and
// records every attempt it sees.
func hookAt(point pg.Point, times uint64, f func(pg.Attempt)) (pg.Hook, *recorder) {
	r := &recorder{}
	hook := func(a pg.Attempt) {
		r.mu.Lock()
		r.seen = append(r.seen, a)
		r.mu.Unlock()
		if a.Point == point && r.fired.Add(1) <= times {
			f(a)
		}
	}
	return hook, r
}

func (r *recorder) at(point pg.Point) []pg.Attempt {
	r.mu.Lock()
	defer r.mu.Unlock()
	out := []pg.Attempt{}
	for _, a := range r.seen {
		if a.Point == point {
			out = append(out, a)
		}
	}
	return out
}

func config(maxAttempts int, tenantLock bool, hook pg.Hook) pg.Config {
	c := pg.DefaultConfig()
	c.MaxAttempts, c.TenantLock, c.Hook = maxAttempts, tenantLock, hook
	return c
}

// fault is what the proxy does with the next COMMIT it relays.
type fault int

const (
	// dropBefore closes both sides without sending COMMIT: the server rolls back.
	dropBefore fault = iota
	// dropAfter sends COMMIT, waits for the server's answer, then closes both sides without
	// relaying it.
	dropAfter
)

// outcome is what the server answered a COMMIT the proxy kept from the client.
type outcome int

const (
	notSent outcome = iota
	committed
	failed
)

// proxy is a TCP proxy in front of the server's Unix socket that can lose the next COMMIT. It
// reads the frontend protocol (the startup message, then typed messages) and acts on a
// simple-query `COMMIT`, which is how the engine commits.
type proxy struct {
	port     int
	mu       sync.Mutex
	faults   []fault
	outcomes []outcome
}

func startProxy(t *testing.T) *proxy {
	socket := pgtest.Start(t).Socket()
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = listener.Close() })
	p := &proxy{port: listener.Addr().(*net.TCPAddr).Port}
	go func() {
		for {
			client, err := listener.Accept()
			if err != nil {
				return
			}
			go func() {
				server, err := net.Dial("unix", socket)
				if err != nil {
					_ = client.Close()
					return
				}
				p.relay(client, server)
			}()
		}
	}()
	return p
}

func (p *proxy) arm(f fault) {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.faults = append(p.faults, f)
}

func (p *proxy) record(o outcome) {
	p.mu.Lock()
	defer p.mu.Unlock()
	p.outcomes = append(p.outcomes, o)
}

func (p *proxy) seen() []outcome {
	p.mu.Lock()
	defer p.mu.Unlock()
	return append([]outcome{}, p.outcomes...)
}

func (p *proxy) next() (fault, bool) {
	p.mu.Lock()
	defer p.mu.Unlock()
	if len(p.faults) == 0 {
		return 0, false
	}
	f := p.faults[0]
	p.faults = p.faults[1:]
	return f, true
}

// url is the engine role's connection string to database through the proxy.
func (p *proxy) url(database string) string {
	return fmt.Sprintf("host=127.0.0.1 port=%d user=%s dbname=%s sslmode=disable",
		p.port, pgtest.EngineRole, database)
}

// nextMessage is the next whole message in buf: the untyped startup message first, then
// messages of a type byte, a length and a body.
func nextMessage(buf *[]byte, typed bool) []byte {
	head, lenAt := 4, 0
	if typed {
		head, lenAt = 5, 1
	}
	if len(*buf) < head {
		return nil
	}
	total := int(binary.BigEndian.Uint32((*buf)[lenAt:lenAt+4])) + lenAt
	if len(*buf) < total {
		return nil
	}
	m := append([]byte{}, (*buf)[:total]...)
	*buf = (*buf)[total:]
	return m
}

func (p *proxy) relay(client, server net.Conn) {
	var closeOnce sync.Once
	closeBoth := func() {
		closeOnce.Do(func() {
			_ = client.Close()
			_ = server.Close()
		})
	}
	defer closeBoth()
	var swallowing atomic.Bool
	go func() {
		defer closeBoth()
		var fromServer []byte
		sawCommit := false
		b := make([]byte, 16384)
		for {
			n, err := server.Read(b)
			if err != nil {
				return
			}
			if !swallowing.Load() {
				if _, err := client.Write(b[:n]); err != nil {
					return
				}
				continue
			}
			fromServer = append(fromServer, b[:n]...)
			for m := nextMessage(&fromServer, true); m != nil; m = nextMessage(&fromServer, true) {
				// Answers to messages sent before COMMIT may come first. COMMIT ends with
				// ReadyForQuery `I`: outside a transaction.
				if m[0] == 'C' && bytes.HasPrefix(m[5:], []byte("COMMIT")) {
					sawCommit = true
				}
				if m[0] == 'Z' && len(m) > 5 && m[5] == 'I' {
					if sawCommit {
						p.record(committed)
					} else {
						p.record(failed)
					}
					return
				}
			}
		}
	}()
	var fromClient []byte
	started := false
	a := make([]byte, 16384)
	for {
		n, err := client.Read(a)
		if err != nil {
			return
		}
		fromClient = append(fromClient, a[:n]...)
		for m := nextMessage(&fromClient, started); m != nil; m = nextMessage(&fromClient, started) {
			started = true
			if m[0] == 'Q' && bytes.Equal(m[5:], []byte("COMMIT\x00")) {
				if f, ok := p.next(); ok {
					switch f {
					case dropBefore:
						p.record(notSent)
						return
					case dropAfter:
						swallowing.Store(true)
					}
				}
			}
			if _, err := server.Write(m); err != nil {
				return
			}
		}
	}
}
