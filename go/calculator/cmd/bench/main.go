// Command bench times one command through the memory engine for tenants of several sizes.
package main

import (
	"fmt"
	"time"

	"github.com/conao3/lean-leanharbor/go/calculator"
	"github.com/conao3/lean-leanharbor/go/calculator/kernel"
)

type request struct {
	actor kernel.Principal
	cmd   kernel.Command
}

func commands(users uint64, count int) []request {
	state := uint64(0x9e37_79b9_7f4a_7c15)
	next := func() uint64 {
		state ^= state << 13
		state ^= state >> 7
		state ^= state << 17
		return state
	}
	out := make([]request, count)
	for i := range out {
		out[i].actor = kernel.Principal{Org: 1, User: next() % users}
		switch next() % 4 {
		case 0:
			out[i].cmd = kernel.CommandSet{Value: next() % 1000}
		case 1:
			out[i].cmd = kernel.CommandApply{Op: kernel.OpAdd, Arg: next() % 1000}
		case 2:
			out[i].cmd = kernel.CommandApply{Op: kernel.OpDiv, Arg: 1 + next()%9}
		default:
			out[i].cmd = kernel.CommandGet{}
		}
	}
	return out
}

func main() {
	for _, users := range []uint64{1, 100, 10_000} {
		count := 200_000
		if users == 10_000 {
			count = 2_000
		}
		engine := calculator.NewEngine()
		for user := range users {
			_, _, _ = engine.Execute(kernel.Principal{Org: 1, User: user}, kernel.CommandSet{Value: 1}, nil)
		}
		cmds := commands(users, count)
		start := time.Now()
		for _, c := range cmds {
			_, _, _ = engine.Execute(c.actor, c.cmd, nil)
		}
		nanos := float64(time.Since(start).Nanoseconds()) / float64(count)
		fmt.Printf("%-36s users=%-6d %10.0f ns/command\n", "memory engine", users, nanos)
	}
}
