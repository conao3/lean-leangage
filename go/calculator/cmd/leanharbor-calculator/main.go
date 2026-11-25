// Command leanharbor-calculator serves the calculator, or with LEANHARBOR_ISSUE prints a
// one-day token and exits. With LEANHARBOR_DATABASE_URL it stores the numbers in PostgreSQL;
// with LEANHARBOR_LOCKDOWN=<owner>:<engine role> and an administrator's connection string it
// creates the tables for those roles and exits.
package main

import (
	"fmt"
	"net/http"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/conao3/lean-leanharbor/go/calculator"
	"github.com/conao3/lean-leanharbor/go/leanharbor"
	"github.com/conao3/lean-leanharbor/go/leanharbor/pg"
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
	secret := []byte(required("LEANHARBOR_SECRET"))
	if who, ok := os.LookupEnv("LEANHARBOR_ISSUE"); ok {
		org, user, _ := strings.Cut(who, ":")
		tenant, errTenant := strconv.ParseUint(org, 10, 64)
		id, errUser := strconv.ParseUint(user, 10, 64)
		if errTenant != nil || errUser != nil {
			fmt.Fprintln(os.Stderr, "LEANHARBOR_ISSUE must be <org>:<user>")
			os.Exit(252)
		}
		expiry := uint64(time.Now().Unix()) + 86_400
		fmt.Println(leanharbor.Issue(secret, leanharbor.Claims{Tenant: tenant, User: id, Expiry: expiry}))
		return
	}
	database, stored := os.LookupEnv("LEANHARBOR_DATABASE_URL")
	if roles, ok := os.LookupEnv("LEANHARBOR_LOCKDOWN"); ok {
		owner, engine, found := strings.Cut(roles, ":")
		if !stored || !found {
			fmt.Fprintln(os.Stderr, "LEANHARBOR_LOCKDOWN=<owner>:<engine role> needs LEANHARBOR_DATABASE_URL")
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
			fmt.Fprintf(os.Stderr, "LEANHARBOR_DATABASE_URL: %v\n", err)
			os.Exit(255)
		}
		rpc = leanharbor.RpcHandler(engine, calculator.Calculator{}, secret)
	} else {
		rpc = leanharbor.RpcHandler(calculator.NewEngine(), calculator.Calculator{}, secret)
	}
	mux := http.NewServeMux()
	mux.HandleFunc("GET /healthz", func(w http.ResponseWriter, _ *http.Request) {
		_, _ = w.Write([]byte("ok"))
	})
	mux.Handle("POST /rpc", rpc)
	if err := http.ListenAndServe(required("LEANHARBOR_LISTEN"), mux); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
