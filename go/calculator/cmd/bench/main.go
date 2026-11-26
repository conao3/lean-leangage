// Command bench times one command through the memory engine for tenants of several sizes, and
// the commands of several tenants run from one goroutine and from a goroutine per tenant.
package main

import (
	"fmt"
	"runtime"
	"sync"
	"time"

	"github.com/conao3/lean-leangage/go/calculator"
	"github.com/conao3/lean-leangage/go/calculator/kernel"
)

type request struct {
	actor kernel.Principal
	cmd   kernel.Command
}

func commands(org, users uint64, count int) []request {
	state := uint64(0x9e37_79b9_7f4a_7c15) + org
	next := func() uint64 {
		state ^= state << 13
		state ^= state >> 7
		state ^= state << 17
		return state
	}
	out := make([]request, count)
	for i := range out {
		out[i].actor = kernel.Principal{Org: org, User: next() % users}
		switch next() % 4 {
		case 0:
			out[i].cmd = kernel.CommandSet{Value: next() % 1000}
		case 1:
			out[i].cmd = kernel.CommandApply{Op: kernel.OpAdd(), Arg: next() % 1000}
		case 2:
			out[i].cmd = kernel.CommandApply{Op: kernel.OpDiv(), Arg: 1 + next()%9}
		default:
			out[i].cmd = kernel.CommandGet{}
		}
	}
	return out
}

func prepared(orgs, users uint64) *calculator.Engine {
	engine := calculator.NewEngine()
	for org := 1; org <= int(orgs); org++ {
		for user := range users {
			_, _, _ = engine.Execute(kernel.Principal{Org: uint64(org), User: user}, kernel.CommandSet{Value: 1}, nil)
		}
	}
	return engine
}

// parallel is the commands per second of count commands to each of tenants tenants of users
// users, from one goroutine when serial and from a goroutine per tenant otherwise.
func parallel(tenants, users uint64, count int, serial bool) float64 {
	engine := prepared(tenants, users)
	defer engine.Close()
	cmds := make([][]request, tenants)
	for i := range cmds {
		cmds[i] = commands(uint64(i+1), users, count)
	}
	start := time.Now()
	if serial {
		for i := range count {
			for _, own := range cmds {
				_, _, _ = engine.Execute(own[i].actor, own[i].cmd, nil)
			}
		}
	} else {
		var group sync.WaitGroup
		for _, own := range cmds {
			group.Go(func() {
				for _, c := range own {
					_, _, _ = engine.Execute(c.actor, c.cmd, nil)
				}
			})
		}
		group.Wait()
	}
	return float64(int(tenants)*count) / time.Since(start).Seconds()
}

func main() {
	for _, users := range []uint64{1, 100, 1_000, 10_000} {
		count := 200_000
		engine := prepared(1, users)
		cmds := commands(1, users, count)
		var before, after runtime.MemStats
		runtime.GC()
		runtime.ReadMemStats(&before)
		start := time.Now()
		for _, c := range cmds {
			_, _, _ = engine.Execute(c.actor, c.cmd, nil)
		}
		nanos := float64(time.Since(start).Nanoseconds()) / float64(count)
		runtime.ReadMemStats(&after)
		allocs := float64(after.Mallocs-before.Mallocs) / float64(count)
		fmt.Printf("%-36s users=%-6d %10.0f ns/command\n", "memory engine", users, nanos)
		fmt.Printf("%-36s users=%-6d %10.1f allocs/command\n", "  allocations", users, allocs)
		engine.Close()
	}
	const tenants, users, count = 8, 100, 100_000
	one := parallel(tenants, users, count, true)
	each := parallel(tenants, users, count, false)
	fmt.Printf("%-36s tenants=%d users=%d %10.0f commands/s\n", "memory engine, 1 goroutine", tenants, users, one)
	fmt.Printf("%-36s tenants=%d users=%d %10.0f commands/s (%.2fx)\n", "memory engine, a goroutine per tenant", tenants, users, each, each/one)
}
