#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"

echo "Building C++ RMQ..."
c++ -O2 -std=c++20 -o bench/rmq bench/rmq.cpp

echo "Building Lean RMQ..."
lake build rmq-bench

echo "Running verification (N=1000, Q=1000)..."
go run bench/runner.go -n 1000 -q 1000 -runs 1 \
  bench/rmq .lake/build/bin/rmq-bench "python3 bench/sparsetable.py" "python3 bench/sqrttree.py"
