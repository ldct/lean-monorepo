// runner.go — Uniform RMQ benchmark runner.
//
// Usage:
//
//	go run bench/runner.go bench/rmq .lake/build/bin/rmq-bench "python3 sparsetable.py" "python3 sqrttree.py"
//
// Flags: -n 1000000 -q 1000000 -runs 3 -seed 42
//
// Full sweep (1e3 through 1e6):
//
//	for exp in 3 4 5 6; do
//	  n=$((10**exp))
//	  echo ">>> N=$n Q=$n <<<"
//	  go run bench/runner.go -n $n -q $n -runs 3 \
//	    bench/rmq .lake/build/bin/rmq-bench "python3 sparsetable.py" "python3 sqrttree.py"
//	  echo
//	done
//
// Results (median of 3 runs, seed=42, Apple M1):
//
//	N=Q     | C++ (rmq) | Lean      | Py SparseTable | Py SqrtTree
//	--------+-----------+-----------+----------------+------------
//	1e3     |       3ms |      34ms |           27ms |        29ms
//	1e4     |       3ms |      39ms |           46ms |        58ms
//	1e5     |       6ms |      86ms |          282ms |       379ms
//	1e6     |      33ms |     763ms |         3021ms |      3999ms
package main

import (
	"bytes"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"sort"
	"strconv"
	"strings"
	"time"
)

type checksumKey struct{ n, q int; seed int64 }

// Known checksums for (n, q, seed=42) — deterministic from the Go RNG.
var knownChecksums = map[checksumKey]string{
	{1_000, 1_000, 42}:         "12062723026",
	{10_000, 10_000, 42}:       "13256664439",
	{100_000, 100_000, 42}:     "17077952648",
	{1_000_000, 1_000_000, 42}: "26760216643",
}

func main() {
	n := flag.Int("n", 1_000_000, "array size")
	q := flag.Int("q", 1_000_000, "number of queries")
	runs := flag.Int("runs", 3, "number of runs per SUT")
	seed := flag.Int64("seed", 42, "RNG seed")
	flag.Parse()

	suts := flag.Args()
	if len(suts) == 0 {
		fmt.Fprintln(os.Stderr, "usage: go run bench/runner.go [flags] <sut-command>...")
		os.Exit(1)
	}

	fmt.Printf("Generating input: N=%d, Q=%d, seed=%d\n", *n, *q, *seed)
	input := generateInput(*n, *q, *seed)
	fmt.Printf("Input size: %.1f MB\n\n", float64(len(input))/(1024*1024))

	expected, hasExpected := knownChecksums[checksumKey{*n, *q, *seed}]

	for _, sut := range suts {
		fmt.Printf("=== %s ===\n", sut)
		times := make([]time.Duration, 0, *runs)
		var lastOutput string
		for i := 0; i < *runs; i++ {
			d, output, err := runSUT(sut, input)
			if err != nil {
				fmt.Printf("  run %d: ERROR: %v\n", i+1, err)
				continue
			}
			times = append(times, d)
			lastOutput = strings.TrimSpace(output)
			fmt.Printf("  run %d: %dms\n", i+1, d.Milliseconds())
		}
		if len(times) > 0 {
			sort.Slice(times, func(i, j int) bool { return times[i] < times[j] })
			median := times[len(times)/2]
			fmt.Printf("  min=%dms  median=%dms  checksum=%s\n", times[0].Milliseconds(), median.Milliseconds(), lastOutput)
			if hasExpected && lastOutput != expected {
				fmt.Printf("CHECKSUM WRONG: got %s, expected %s\n", lastOutput, expected)
				os.Exit(1)
			}
		}
		fmt.Println()
	}

	if hasExpected {
		fmt.Printf("Checksum verified: %s\n", expected)
	}
}

func generateInput(n, q int, seed int64) []byte {
	rng := rand.New(rand.NewSource(seed))
	var buf bytes.Buffer
	// Pre-size the buffer: rough estimate
	buf.Grow(n*6 + q*14 + 64)

	buf.WriteString(strconv.Itoa(n))
	buf.WriteByte(' ')
	buf.WriteString(strconv.Itoa(q))
	buf.WriteByte('\n')

	for i := 0; i < n; i++ {
		if i > 0 {
			buf.WriteByte(' ')
		}
		buf.WriteString(strconv.Itoa(rng.Intn(1_000_000_000)))
	}
	buf.WriteByte('\n')

	for i := 0; i < q; i++ {
		a := rng.Intn(n)
		b := rng.Intn(n)
		if a > b {
			a, b = b, a
		}
		buf.WriteString(strconv.Itoa(a))
		buf.WriteByte(' ')
		buf.WriteString(strconv.Itoa(b))
		buf.WriteByte('\n')
	}

	return buf.Bytes()
}

func runSUT(command string, input []byte) (time.Duration, string, error) {
	parts := strings.Fields(command)
	cmd := exec.Command(parts[0], parts[1:]...)
	cmd.Stdin = bytes.NewReader(input)
	cmd.Env = append(os.Environ(), "LEAN_STACK_SIZE=536870912") // 512 MB

	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	start := time.Now()
	err := cmd.Run()
	elapsed := time.Since(start)

	if err != nil {
		return 0, "", fmt.Errorf("%v\nstderr: %s", err, stderr.String())
	}

	return elapsed, stdout.String(), nil
}
