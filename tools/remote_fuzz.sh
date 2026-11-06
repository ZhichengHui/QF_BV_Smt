#!/usr/bin/env bash
# Usage: tools/remote_fuzz.sh N SEED...
# Copies the release binary and fuzz.py to the compute host and runs fuzz.py against z3 there,
# one process per seed, N problems each. Prints each run's result.
set -euo pipefail
N=$1; shift
HERE=$(cd "$(dirname "$0")/.." && pwd)
W=/disk/scratch/s2982359/bvsmt-fuzz
Z3=/disk/scratch/s2982359/verus/z3
tar -czf - -C "$HERE/target/release" bvsmt -C "$HERE/tools" fuzz.py | \
  ssh -o ConnectTimeout=15 -J s2982359@ssh.inf.ed.ac.uk s2982359@s2982359.pgr.inf.ed.ac.uk \
  "mkdir -p $W && tar -C $W -xzf - && cd $W && \
   for s in $*; do timeout 3000 python3 fuzz.py ./bvsmt $Z3 $N \$s > out\$s.txt 2>&1 & done; wait; \
   for s in $*; do echo \"seed \$s: \$(head -c 3000 out\$s.txt)\"; done" 2>&1 \
  | grep -v -i "post-quantum\|store now\|upgraded\|pq.html"
