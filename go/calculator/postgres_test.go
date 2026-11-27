package calculator

// The calculator on the PostgreSQL engine: the shared command list gives the replies of the
// memory engine and of Lean, the commands of one tenant leave the rows of the others as they
// were, a server started again on the same database answers from the state the first one
// stored, and the Rust and the Go servers answer from one database what the other stored.

import (
	"context"
	"fmt"
	"io"
	"maps"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/jackc/pgx/v5"

	"github.com/conao3/lean-leangage/go/calculator/gen/kernel"
	"github.com/conao3/lean-leangage/go/leangage"
	"github.com/conao3/lean-leangage/go/leangage/pg"
	"github.com/conao3/lean-leangage/go/leangage/pg/pgtest"
)

const secret = "secret"

// The rows stored and read back in PostgreSQL give every command the reply the memory engine
// and Lean give it: PostgreSQL runs the generated statements as the model of `Leangage.Sql`
// says. The engine that remembers no snapshot reads the rows back for every command; the one
// that remembers them gives the same replies.
func TestPostgresEngineAgreesWithMemoryEngineAndLean(t *testing.T) {
	t.Parallel()
	lines, want := commands(t)
	for _, c := range []struct {
		name  string
		cache int
	}{{"calculator_differential", 0}, {"calculator_differential_cached", 1024}} {
		url := pgtest.Start(t).Locked(t, Calculator{}.Tables(), c.name)
		config := pg.DefaultConfig()
		config.CacheTenants = c.cache
		engine, err := ConnectEngine(url, 2, config)
		if err != nil {
			t.Fatalf("the engine connects: %v", err)
		}
		memory := NewEngine()
		for i, line := range lines {
			actor, cmd := parse(t, line)
			ours := answer(engine.Execute(actor, cmd, nil))
			theirs := answer(memory.Execute(actor, cmd, nil))
			if ours != theirs || ours != want[i] {
				t.Fatalf("cache %d, line %d: %s: PostgreSQL %s, memory %s, Lean %s",
					c.cache, i+1, line, ours, theirs, want[i])
			}
		}
		s := engine.Stats()
		if s.Retries != 0 {
			t.Fatalf("cache %d: %d retries", c.cache, s.Retries)
		}
		if c.cache == 0 && s.Loads != s.Attempts {
			t.Fatalf("every attempt reads the rows: %+v", s)
		}
		memory.Close()
		engine.Close()
	}
}

// The PostgreSQL engine releases the snapshot it loads for each command and the write set it
// compiles: the commands of the shared command list, refused ones among them, leak no value.
func TestPostgresEngineLeaksNoValue(t *testing.T) {
	lines, want := commands(t)
	url := pgtest.Start(t).Locked(t, Calculator{}.Tables(), "calculator_leaks")
	engine, err := ConnectEngine(url, 2, pg.DefaultConfig())
	if err != nil {
		t.Fatalf("the engine connects: %v", err)
	}
	defer engine.Close()
	leaked := trackLeaks(t)
	for i, line := range lines[:1000] {
		actor, cmd := parse(t, line)
		if got := answer(engine.Execute(actor, cmd, nil)); got != want[i] {
			t.Fatalf("line %d: %s: got %s, want %s", i+1, line, got, want[i])
		}
	}
	if n := leaked(); n != 0 {
		t.Fatalf("%d values leaked", n)
	}
}

type userKey struct{ tenant, user int64 }

func memories(t *testing.T, conn *pgx.Conn) map[userKey]int64 {
	t.Helper()
	rows, err := conn.Query(context.Background(), `SELECT tenant_id, "user", value FROM memories`)
	if err != nil {
		t.Fatal(err)
	}
	out := map[userKey]int64{}
	for rows.Next() {
		var k userKey
		var v int64
		if err := rows.Scan(&k.tenant, &k.user, &v); err != nil {
			t.Fatal(err)
		}
		out[k] = v
	}
	if err := rows.Err(); err != nil {
		t.Fatal(err)
	}
	return out
}

// The command list mixes three tenants. After each command, every row of the other tenants,
// and of the other users of its tenant, is as it was.
func TestTenantsLeaveEachOtherRows(t *testing.T) {
	t.Parallel()
	lines, _ := commands(t)
	c := pgtest.Start(t)
	name := "calculator_isolation"
	url := c.Locked(t, Calculator{}.Tables(), name)
	engine, err := ConnectEngine(url, 2, pg.DefaultConfig())
	if err != nil {
		t.Fatalf("the engine connects: %v", err)
	}
	defer engine.Close()
	others := func(rows map[userKey]int64, mine userKey) map[userKey]int64 {
		out := maps.Clone(rows)
		delete(out, mine)
		return out
	}
	admin := pgtest.Connect(t, c.AdminURL(name))
	before := memories(t, admin)
	tenants := map[uint64]bool{}
	for _, line := range lines {
		actor, cmd := parse(t, line)
		tenants[actor.Org] = true
		mine := userKey{int64(actor.Org), int64(actor.User)}
		if _, _, err := engine.Execute(actor, cmd, nil); err != nil {
			t.Fatal(err)
		}
		after := memories(t, admin)
		if !maps.Equal(others(after, mine), others(before, mine)) {
			t.Fatalf("%s changed the rows of others", line)
		}
		before = after
	}
	stored := map[int64]bool{}
	for k := range before {
		stored[k.tenant] = true
	}
	if len(tenants) != 3 || len(stored) != 3 {
		t.Fatalf("%d tenants, %d stored", len(tenants), len(stored))
	}
}

type server struct {
	name string
	cmd  *exec.Cmd
	addr string
}

// goServer is the Go calculator server, built for this test.
func goServer(t *testing.T) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), "leangage-calculator")
	build := exec.Command("go", "build", "-o", path, "./cmd/leangage-calculator")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("go build: %v\n%s", err, out)
	}
	return path
}

// rustServer is the Rust calculator server that the Makefile builds.
func rustServer(t *testing.T) string {
	t.Helper()
	path, ok := os.LookupEnv("LEANGAGE_RUST_CALCULATOR")
	if !ok {
		t.Fatal("LEANGAGE_RUST_CALCULATOR is required")
	}
	return path
}

func freeAddr(t *testing.T) string {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer func() { _ = l.Close() }()
	return l.Addr().String()
}

func startServer(t *testing.T, name, binary, url string) *server {
	t.Helper()
	addr := freeAddr(t)
	cmd := exec.Command(binary)
	cmd.Env = append(os.Environ(), "LEANGAGE_SECRET="+secret, "LEANGAGE_LISTEN="+addr,
		"LEANGAGE_DATABASE_URL="+url)
	cmd.Stdout, cmd.Stderr = os.Stdout, os.Stderr
	if err := cmd.Start(); err != nil {
		t.Fatalf("the %s server starts: %v", name, err)
	}
	s := &server{name, cmd, addr}
	t.Cleanup(s.stop)
	start := time.Now()
	for {
		conn, err := net.Dial("tcp", addr)
		if err == nil {
			_ = conn.Close()
			return s
		}
		if time.Since(start) > 20*time.Second {
			t.Fatalf("the %s server does not listen", name)
		}
		time.Sleep(20 * time.Millisecond)
	}
}

func (s *server) stop() {
	if s.cmd.ProcessState == nil {
		_ = s.cmd.Process.Kill()
		_ = s.cmd.Wait()
	}
}

// lockdown runs binary with LEANGAGE_LOCKDOWN and the administrator's connection string.
func lockdown(t *testing.T, binary, adminURL string) {
	t.Helper()
	cmd := exec.Command(binary)
	cmd.Env = append(os.Environ(), "LEANGAGE_SECRET="+secret, "LEANGAGE_DATABASE_URL="+adminURL,
		"LEANGAGE_LOCKDOWN="+pgtest.Owner+":"+pgtest.EngineRole)
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("lockdown: %v\n%s", err, out)
	}
}

func bearer(tenant, user uint64) string {
	expiry := uint64(time.Now().Unix()) + 86_400
	return leangage.Issue([]byte(secret), leangage.Claims{Tenant: tenant, User: user, Expiry: expiry})
}

type response struct {
	status int
	body   string
}

func (s *server) post(t *testing.T, token, key, body string) response {
	t.Helper()
	req, err := http.NewRequest(http.MethodPost, "http://"+s.addr+"/rpc", strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	req.Header.Set("Authorization", "Bearer "+token)
	req.Header.Set("Content-Type", "application/json")
	if key != "" {
		req.Header.Set("Idempotency-Key", key)
	}
	res, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("%s server: %v", s.name, err)
	}
	defer func() { _ = res.Body.Close() }()
	got, err := io.ReadAll(res.Body)
	if err != nil {
		t.Fatal(err)
	}
	return response{res.StatusCode, string(got)}
}

func TestStateSurvivesARestartOfTheServer(t *testing.T) {
	t.Parallel()
	c := pgtest.Start(t)
	name := "calculator_restart"
	url := c.Database(t, name)
	binary := goServer(t)
	lockdown(t, binary, c.AdminURL(name))
	a, b := bearer(1, 7), bearer(2, 7)
	first := startServer(t, "Go", binary, url)
	for _, step := range []struct {
		token, body string
		want        response
	}{
		{a, `{"cmd":"set","value":6}`, response{200, `{"value":6}`}},
		{a, `{"cmd":"apply","op":"mul","arg":7}`, response{200, `{"value":42}`}},
		{a, `{"cmd":"apply","op":"div","arg":0}`, response{422, `{"error":"division_by_zero"}`}},
		{b, `{"cmd":"set","value":5}`, response{200, `{"value":5}`}},
	} {
		if got := first.post(t, step.token, "", step.body); got != step.want {
			t.Fatalf("%s: got %v, want %v", step.body, got, step.want)
		}
	}
	first.stop()
	second := startServer(t, "Go", binary, url)
	for _, step := range []struct {
		token string
		want  response
	}{
		{a, response{200, `{"value":42}`}},
		{b, response{200, `{"value":5}`}},
		{bearer(1, 8), response{200, `{"value":0}`}},
	} {
		if got := second.post(t, step.token, "", `{"cmd":"get"}`); got != step.want {
			t.Fatalf("get: got %v, want %v", got, step.want)
		}
	}
	conn := pgtest.Connect(t, c.AdminURL(name))
	var owner string
	err := conn.QueryRow(context.Background(), "SELECT tableowner FROM pg_tables WHERE tablename = 'memories'").Scan(&owner)
	if err != nil || owner != pgtest.Owner {
		t.Fatalf("owner %q: %v", owner, err)
	}
}

// body is the JSON of a line of the command list.
func body(t *testing.T, line string) string {
	t.Helper()
	words := strings.Split(line, " ")
	switch words[2] {
	case "set":
		return fmt.Sprintf(`{"cmd":"set","value":%s}`, words[3])
	case "apply":
		return fmt.Sprintf(`{"cmd":"apply","op":"%s","arg":%s}`, words[3], words[4])
	case "get":
		return `{"cmd":"get"}`
	}
	t.Fatalf("bad line %s", line)
	return ""
}

// expected is the response to a command the oracle answered with want.
func expected(t *testing.T, want string) response {
	t.Helper()
	if v, ok := strings.CutPrefix(want, "ok "); ok {
		return response{200, fmt.Sprintf(`{"value":%s}`, v)}
	}
	if name, ok := strings.CutPrefix(want, "error "); ok {
		return response{422, fmt.Sprintf(`{"error":"%s"}`, name)}
	}
	t.Fatalf("bad oracle line %s", want)
	return response{}
}

// The Rust server makes the tables (LEANGAGE_LOCKDOWN), and the Rust and the Go servers run
// on that database together. The commands of the shared command list go to the two servers in
// turn, so that each command reads what the other server stored, and every response is the one
// Lean gives. Every tenth command carries an idempotency key and is sent again with that key to
// the other server, which replays the stored reply (a refusal, which is not stored, is decided
// again the same way); the key with another command is refused by the other server. At the end
// both servers answer `get` alike for every user.
func TestRustAndGoServersShareADatabase(t *testing.T) {
	t.Parallel()
	rustBinary, goBinary := rustServer(t), goServer(t)
	lines, want := commands(t)
	c := pgtest.Start(t)
	name := "calculator_shared"
	url := c.Database(t, name)
	lockdown(t, rustBinary, c.AdminURL(name))
	servers := []*server{
		startServer(t, "Rust", rustBinary, url),
		startServer(t, "Go", goBinary, url),
	}
	tokens := map[kernel.Principal]string{}
	replays := 0
	for i, line := range lines {
		actor, cmd := parse(t, line)
		token, ok := tokens[actor]
		if !ok {
			token = bearer(actor.Org, actor.User)
			tokens[actor] = token
		}
		this, other := servers[i%2], servers[(i+1)%2]
		sent, expect := body(t, line), expected(t, want[i])
		key := ""
		if i%10 == 0 {
			key = fmt.Sprintf("k%d", i)
		}
		if got := this.post(t, token, key, sent); got != expect {
			t.Fatalf("line %d: %s: the %s server answered %v, want %v", i+1, line, this.name, got, expect)
		}
		if key == "" {
			continue
		}
		if got := other.post(t, token, key, sent); got != expect {
			t.Fatalf("line %d: %s: the %s server answered the key with %v, want %v", i+1, line, other.name, got, expect)
		}
		if expect.status != 200 {
			continue
		}
		replays++
		another := `{"cmd":"get"}`
		if _, isGet := cmd.(kernel.CommandGet); isGet {
			another = `{"cmd":"set","value":0}`
		}
		reused := response{422, `{"error":"idempotency key reused"}`}
		if got := other.post(t, token, key, another); got != reused {
			t.Fatalf("line %d: the %s server answered the key with another command: %v", i+1, other.name, got)
		}
	}
	var stored int
	admin := pgtest.Connect(t, c.AdminURL(name))
	if err := admin.QueryRow(context.Background(), "SELECT count(*) FROM leangage_idempotency").Scan(&stored); err != nil {
		t.Fatal(err)
	}
	if replays == 0 || stored != replays {
		t.Fatalf("%d keyed commands accepted, %d replies stored", replays, stored)
	}
	for actor, token := range tokens {
		rust := servers[0].post(t, token, "", `{"cmd":"get"}`)
		golang := servers[1].post(t, token, "", `{"cmd":"get"}`)
		if rust != golang || rust.status != 200 {
			t.Fatalf("%+v: Rust %v, Go %v", actor, rust, golang)
		}
	}
}

// The Go engine and the Rust server, in a process of its own, on one database: after each write
// of the one, the other reads the rows it wrote, on the read-only and on the write path, while
// the engine reads no row after its own commits. Then each adds 1 from four goroutines at once,
// and both read the sum.
func TestEngineReadsWhatTheRustServerWrote(t *testing.T) {
	t.Parallel()
	rustBinary := rustServer(t)
	c := pgtest.Start(t)
	name := "calculator_other_writer"
	url := c.Database(t, name)
	lockdown(t, rustBinary, c.AdminURL(name))
	rust := startServer(t, "Rust", rustBinary, url)
	engine, err := ConnectEngine(url, 4, pg.DefaultConfig())
	if err != nil {
		t.Fatalf("the engine connects: %v", err)
	}
	defer engine.Close()
	who := kernel.Principal{Org: 3, User: 1}
	token := bearer(3, 1)
	add := kernel.CommandApply{Op: kernel.OpAdd(), Arg: 1}
	value := func(cmd kernel.Command) uint64 {
		t.Helper()
		reply, refusal, err := engine.Execute(who, cmd, nil)
		if err != nil || refusal != nil {
			t.Fatalf("%v: %v %v", cmd, refusal, err)
		}
		return reply.V
	}
	expect := func(got response, want string) {
		t.Helper()
		if got != (response{200, want}) {
			t.Fatalf("Rust server: got %+v, want %s", got, want)
		}
	}
	if got := value(kernel.CommandSet{Value: 6}); got != 6 {
		t.Fatalf("set: %d", got)
	}
	expect(rust.post(t, token, "", `{"cmd":"apply","op":"add","arg":4}`), `{"value":10}`)
	if got := value(kernel.CommandGet{}); got != 10 {
		t.Fatalf("read-only path: %d", got)
	}
	expect(rust.post(t, token, "", `{"cmd":"apply","op":"mul","arg":3}`), `{"value":30}`)
	if got := value(add); got != 31 {
		t.Fatalf("write path: %d", got)
	}
	expect(rust.post(t, token, "", `{"cmd":"get"}`), `{"value":31}`)
	loads := engine.Stats().Loads
	if value(add) != 32 || value(kernel.CommandGet{}) != 32 || engine.Stats().Loads != loads {
		t.Fatalf("its own commit is not remembered: %+v", engine.Stats())
	}
	done := make(chan error, 8)
	for range 4 {
		go func() {
			for range 50 {
				if _, refusal, err := engine.Execute(who, add, nil); err != nil || refusal != nil {
					done <- fmt.Errorf("engine: %v %v", refusal, err)
					return
				}
			}
			done <- nil
		}()
		go func() {
			for range 50 {
				req, err := http.NewRequest(http.MethodPost, "http://"+rust.addr+"/rpc",
					strings.NewReader(`{"cmd":"apply","op":"add","arg":1}`))
				if err != nil {
					done <- err
					return
				}
				req.Header.Set("Authorization", "Bearer "+token)
				req.Header.Set("Content-Type", "application/json")
				res, err := http.DefaultClient.Do(req)
				if err != nil {
					done <- err
					return
				}
				_, _ = io.Copy(io.Discard, res.Body)
				_ = res.Body.Close()
				if res.StatusCode != 200 {
					done <- fmt.Errorf("Rust server: %d", res.StatusCode)
					return
				}
			}
			done <- nil
		}()
	}
	for range 8 {
		if err := <-done; err != nil {
			t.Fatal(err)
		}
	}
	if got := value(kernel.CommandGet{}); got != 432 {
		t.Fatalf("the sum: %d", got)
	}
	expect(rust.post(t, token, "", `{"cmd":"get"}`), `{"value":432}`)
}
