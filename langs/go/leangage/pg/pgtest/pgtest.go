// Package pgtest is a PostgreSQL server for tests, in a temporary directory, one per test
// process.
//
// [Start] runs `initdb` and starts the server on a Unix socket in that directory, with the roles
// [Owner] (no login) and [EngineRole] (login, not a superuser). A shell started with the server
// waits on a pipe from the test process; when the process exits, however it exits, the pipe
// closes and the shell stops the server and removes the directory. `initdb`, `pg_ctl` and `psql`
// come from PATH (the flake's devShell); a test that cannot start the server fails.
package pgtest

import (
	"bufio"
	"bytes"
	"context"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/jackc/pgx/v5"

	"github.com/conao3/lean-leangage/langs/go/leangage/gen/sql"
	"github.com/conao3/lean-leangage/langs/go/leangage/pg"
)

// Owner is the role that owns the tables.
const Owner = "leangage_owner"

// EngineRole is the role the engine logs in as.
const EngineRole = "leangage_engine"

const supervisor = `
set -eu
dir=$1
trap 'pg_ctl -D "$dir/data" -m immediate stop >/dev/null 2>&1 || true; rm -rf "$dir"' EXIT
initdb -D "$dir/data" -U postgres --auth=trust --no-sync -E UTF8 >"$dir/initdb.log" 2>&1
pg_ctl -D "$dir/data" -l "$dir/server.log" -w -o "-k $dir -c listen_addresses='' -c fsync=off -c synchronous_commit=off -c full_page_writes=off -c max_connections=300" start >/dev/null
psql -h "$dir" -U postgres -d postgres -X -q -v ON_ERROR_STOP=1 -c "CREATE ROLE leangage_owner NOLOGIN" -c "CREATE ROLE leangage_engine LOGIN"
echo ready
read _ || true
`

// Cluster is the server of a test process.
type Cluster struct {
	// Dir is the data directory's parent, where the server's socket is.
	Dir string
	// The supervisor's stdin: the server runs while it is open.
	stdin io.WriteCloser
	cmd   *exec.Cmd
}

var (
	once     sync.Once
	cluster  *Cluster
	startErr error
)

// Start is the server of this test process, started on the first call. t fails if it cannot
// start.
func Start(t testing.TB) *Cluster {
	t.Helper()
	once.Do(func() { cluster, startErr = start() })
	if startErr != nil {
		t.Fatal(startErr)
	}
	return cluster
}

func start() (*Cluster, error) {
	dir := fmt.Sprintf("/tmp/leangage-pg-%d-%d", os.Getpid(), time.Now().Nanosecond())
	if err := os.Mkdir(dir, 0o700); err != nil {
		return nil, err
	}
	cmd := exec.Command("sh", "-c", supervisor, "sh", dir)
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return nil, err
	}
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, err
	}
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Start(); err != nil {
		return nil, fmt.Errorf("sh does not start: %w", err)
	}
	line, _ := bufio.NewReader(stdout).ReadString('\n')
	if strings.TrimSpace(line) != "ready" {
		_ = stdin.Close()
		_ = cmd.Wait()
		log := func(name string) string {
			b, _ := os.ReadFile(filepath.Join(dir, name))
			return string(b)
		}
		return nil, fmt.Errorf(
			"PostgreSQL did not start (initdb, pg_ctl and psql must be on PATH):\n%s\n%s\n%s",
			stderr.String(), log("initdb.log"), log("server.log"))
	}
	return &Cluster{Dir: dir, stdin: stdin, cmd: cmd}, nil
}

// URL is a connection string for user to database.
func (c *Cluster) URL(user, database string) string {
	return fmt.Sprintf("host=%s user=%s dbname=%s", c.Dir, user, database)
}

// AdminURL is the superuser's connection string to database.
func (c *Cluster) AdminURL(database string) string {
	return c.URL("postgres", database)
}

// Socket is the Unix socket of the server.
func (c *Cluster) Socket() string {
	return filepath.Join(c.Dir, ".s.PGSQL.5432")
}

// Database creates the empty database name, dropping one of that name, and returns the engine
// role's connection string to it.
func (c *Cluster) Database(t testing.TB, name string) string {
	t.Helper()
	admin := Connect(t, c.AdminURL("postgres"))
	for _, statement := range []string{
		fmt.Sprintf(`DROP DATABASE IF EXISTS "%s" WITH (FORCE)`, name),
		fmt.Sprintf(`CREATE DATABASE "%s"`, name),
	} {
		if _, err := admin.Exec(context.Background(), statement); err != nil {
			t.Fatalf("the database is created: %v", err)
		}
	}
	_ = admin.Close(context.Background())
	return c.URL(EngineRole, name)
}

// Locked is [Cluster.Database], with the tables made by [pg.Lockdown] for [Owner] and
// [EngineRole].
func (c *Cluster) Locked(t testing.TB, tables []sql.Tab, name string) string {
	t.Helper()
	url := c.Database(t, name)
	if err := pg.Lockdown(tables, c.AdminURL(name), Owner, EngineRole); err != nil {
		t.Fatalf("lockdown: %v", err)
	}
	return url
}

// Connect is a connection to url, closed when the test ends.
func Connect(t testing.TB, url string) *pgx.Conn {
	t.Helper()
	conn, err := pgx.Connect(context.Background(), url)
	if err != nil {
		t.Fatalf("the test connects: %v", err)
	}
	t.Cleanup(func() { _ = conn.Close(context.Background()) })
	return conn
}
