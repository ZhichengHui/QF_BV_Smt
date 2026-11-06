#!/usr/bin/env bash
# Usage: tools/check.sh THEORY [TIMEOUT]
# Copies urust/, spec/ and proof/ to the compute host and processes THEORY (a theory name, e.g.
# BVSmt_Proof) and its imports on top of the AutoCorrode heap. Prints Isabelle's messages.
# BVSMT_WORK names the work directory under the scratch disk (default bvsmt-work); use a
# different one for each concurrent check.
set -euo pipefail
T=$1; TO=${2:-3000}
HERE=$(cd "$(dirname "$0")/.." && pwd)
S="ssh -o ConnectTimeout=15 -o ServerAliveInterval=15 -o ServerAliveCountMax=4 -J s2982359@ssh.inf.ed.ac.uk s2982359@s2982359.pgr.inf.ed.ac.uk"
W=/disk/scratch/s2982359/${BVSMT_WORK:-bvsmt-work}
tar -C "$HERE" -czf - urust spec proof 2>/dev/null | $S "rm -rf $W/src && mkdir -p $W/src && tar -C $W/src -xzf - && cd $W/src && \
  timeout $TO ~/isabelle/Isabelle2026/bin/isabelle process_theories -l AutoCorrode -d ~/builds/AutoCorrode \
  -d urust -d spec -d proof -O -m 200 -o threads=8 $T; echo EXIT \$?" 2>&1 \
  | grep -v -i "post-quantum\|store now\|upgraded\|pq.html"
