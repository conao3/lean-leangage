// Command leangage-calculator serves the calculator, or with LEANGAGE_ISSUE prints a
// one-day token and exits. With LEANGAGE_DATABASE_URL it stores the numbers in PostgreSQL;
// with LEANGAGE_LOCKDOWN=<owner>:<engine role> and an administrator's connection string it
// creates the tables for those roles and exits.
package main

import (
	"fmt"
	"net/http"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/conao3/lean-leangage/go/calculator"
	"github.com/conao3/lean-leangage/go/leangage"
	"github.com/conao3/lean-leangage/go/leangage/pg"
)

// poolSize is the number of connections of the PostgreSQL engine's pool.
const poolSize = 16

func required(name string) string {
	value, ok := os.LookupEnv(name)
	if !ok {
		fmt.Fprintf(os.Stderr, "%s is required\n", name)
		os.Exit(255)
	}
	return value
}

func main() {
	secret := []byte(required("LEANGAGE_SECRET"))
	if who, ok := os.LookupEnv("LEANGAGE_ISSUE"); ok {
		org, user, _ := strings.Cut(who, ":")
		tenant, errTenant := strconv.ParseUint(org, 10, 64)
		id, errUser := strconv.ParseUint(user, 10, 64)
		if errTenant != nil || errUser != nil {
			fmt.Fprintln(os.Stderr, "LEANGAGE_ISSUE must be <org>:<user>")
			os.Exit(252)
		}
		expiry := uint64(time.Now().Unix()) + 86_400
		fmt.Println(leangage.Issue(secret, leangage.Claims{Tenant: tenant, User: id, Expiry: expiry}))
		return
	}
	database, stored := os.LookupEnv("LEANGAGE_DATABASE_URL")
	if roles, ok := os.LookupEnv("LEANGAGE_LOCKDOWN"); ok {
		owner, engine, found := strings.Cut(roles, ":")
		if !stored || !found {
			fmt.Fprintln(os.Stderr, "LEANGAGE_LOCKDOWN=<owner>:<engine role> needs LEANGAGE_DATABASE_URL")
			os.Exit(252)
		}
		if err := pg.Lockdown(calculator.Calculator{}.Tables(), database, owner, engine); err != nil {
			fmt.Fprintf(os.Stderr, "lockdown: %v\n", err)
			os.Exit(255)
		}
		return
	}
	var rpc http.Handler
	if stored {
		engine, err := calculator.ConnectEngine(database, poolSize, pg.DefaultConfig())
		if err != nil {
			fmt.Fprintf(os.Stderr, "LEANGAGE_DATABASE_URL: %v\n", err)
			os.Exit(255)
		}
		rpc = leangage.RpcHandler(engine, calculator.Calculator{}, secret)
	} else {
		rpc = leangage.RpcHandler(calculator.NewEngine(), calculator.Calculator{}, secret)
	}
	mux := http.NewServeMux()
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		_, _ = w.Write([]byte("ok"))
	})
	mux.Handle("POST /rpc", rpc)
	if err := http.ListenAndServe(required("LEANGAGE_LISTEN"), mux); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
