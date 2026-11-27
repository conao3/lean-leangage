//! A PostgreSQL server for tests, in a temporary directory, one per test process.
//!
//! [`cluster`] runs `initdb` and starts the server on a Unix socket in that directory, with the
//! roles [`OWNER`] (no login) and [`ENGINE_ROLE`] (login, not a superuser). A shell started with
//! the server waits on a pipe from the test process; when the process exits, however it exits,
//! the pipe closes and the shell stops the server and removes the directory. `initdb`, `pg_ctl`
//! and `psql` come from `PATH` (the flake's devShell); a test that cannot start the server fails.

use std::io::{BufRead, BufReader, Read};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::{Mutex, OnceLock};

use leangage::{EngineError, Storage};
use tokio_postgres::NoTls;

/// The role that owns the tables.
pub const OWNER: &str = "leangage_owner";
/// The role the engine logs in as.
pub const ENGINE_ROLE: &str = "leangage_engine";

const SUPERVISOR: &str = r#"
set -eu
dir=$1
trap 'pg_ctl -D "$dir/data" -m immediate stop >/dev/null 2>&1 || true; rm -rf "$dir"' EXIT
initdb -D "$dir/data" -U postgres --auth=trust --no-sync -E UTF8 >"$dir/initdb.log" 2>&1
pg_ctl -D "$dir/data" -l "$dir/server.log" -w -o "-k $dir -c listen_addresses='' -c fsync=off -c synchronous_commit=off -c full_page_writes=off -c max_connections=300" start >/dev/null
psql -h "$dir" -U postgres -d postgres -X -q -v ON_ERROR_STOP=1 -c "CREATE ROLE leangage_owner NOLOGIN" -c "CREATE ROLE leangage_engine LOGIN"
echo ready
read _ || true
"#;

pub struct Cluster {
    /// The data directory's parent, where the server's socket is.
    pub dir: PathBuf,
    _stdin: Mutex<ChildStdin>,
    _stdout: Mutex<BufReader<ChildStdout>>,
    _supervisor: Mutex<Child>,
}

/// The server of this test process, started on the first call.
pub fn cluster() -> &'static Cluster {
    static CLUSTER: OnceLock<Cluster> = OnceLock::new();
    CLUSTER.get_or_init(start)
}

fn start() -> Cluster {
    let dir = PathBuf::from(format!(
        "/tmp/leangage-pg-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.subsec_nanos())
    ));
    std::fs::create_dir(&dir).expect("the cluster's directory is created");
    let mut child = Command::new("sh")
        .arg("-c")
        .arg(SUPERVISOR)
        .arg("sh")
        .arg(&dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("sh starts");
    let stdin = child.stdin.take().expect("stdin is piped");
    let mut stdout = BufReader::new(child.stdout.take().expect("stdout is piped"));
    let mut line = String::new();
    stdout.read_line(&mut line).expect("the supervisor writes");
    if line.trim() != "ready" {
        let mut err = String::new();
        if let Some(mut e) = child.stderr.take() {
            let _ = e.read_to_string(&mut err);
        }
        let _ = child.wait();
        let log = |name: &str| std::fs::read_to_string(dir.join(name)).unwrap_or_default();
        panic!(
            "PostgreSQL did not start (initdb, pg_ctl and psql must be on PATH):\n{err}\n{}\n{}",
            log("initdb.log"),
            log("server.log")
        );
    }
    Cluster {
        dir,
        _stdin: Mutex::new(stdin),
        _stdout: Mutex::new(stdout),
        _supervisor: Mutex::new(child),
    }
}

impl Cluster {
    /// A connection string for `user` to `database`.
    pub fn url(&self, user: &str, database: &str) -> String {
        format!("host={} user={user} dbname={database}", self.dir.display())
    }

    /// The superuser's connection string to `database`.
    pub fn admin_url(&self, database: &str) -> String {
        self.url("postgres", database)
    }

    /// The Unix socket of the server.
    pub fn socket(&self) -> PathBuf {
        self.dir.join(".s.PGSQL.5432")
    }

    /// Creates the empty database `name`, dropping one of that name, and returns the engine
    /// role's connection string to it.
    pub async fn database(&self, name: &str) -> String {
        let admin = connect(&self.admin_url("postgres")).await;
        for statement in [
            format!("DROP DATABASE IF EXISTS \"{name}\" WITH (FORCE)"),
            format!("CREATE DATABASE \"{name}\""),
        ] {
            admin
                .batch_execute(&statement)
                .await
                .expect("the database is created");
        }
        self.url(ENGINE_ROLE, name)
    }

    /// [`Cluster::database`], with the tables of `K` made by [`crate::lockdown`].
    pub async fn locked<K: Storage>(&self, name: &str) -> String {
        let url = self.database(name).await;
        lockdown::<K>(&self.admin_url(name))
            .await
            .expect("lockdown");
        url
    }
}

async fn lockdown<K: Storage>(admin_url: &str) -> Result<(), EngineError> {
    crate::lockdown::<K>(admin_url, OWNER, ENGINE_ROLE).await
}

/// A connection whose driver runs on a task of its own.
pub async fn connect(url: &str) -> tokio_postgres::Client {
    let (client, connection) = tokio_postgres::connect(url, NoTls)
        .await
        .expect("the test connects");
    tokio::spawn(connection);
    client
}
