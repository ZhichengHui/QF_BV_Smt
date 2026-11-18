#!/usr/bin/env bash
# Usage: bench/run.sh SUITE [SOLVER]
#
# Runs the benchmark suite bench/SUITE (PLAN.md, Benchmarks) on SOLVER (default: the release build
# target/release/qfbv; build it first with `cargo build --release`).
#
# bench/SUITE/suite.sh sets:
#   SOURCE_URL, SOURCE_FILE, SOURCE_MD5   the public archive the instances come from, and its hash
#   TIMEOUT, MEM_GB                       wall-clock seconds and address space (GB) per instance
#   JOBS                                  instances run in parallel (override: BENCH_JOBS)
#   INSTANCES                             one line per instance: "SHA256 STATUS PATH", PATH a member
#                                         of the archive, STATUS its known answer (sat/unsat)
# The archive is downloaded once into the cache (BENCH_CACHE, default bench/cache, not committed),
# the instances are extracted from it and checked against their hashes.
#
# Each instance is run by frontend/tools/eval.py: the answer must match the known answer, and for
# sat the model printed by the solver is checked with z3 (Z3, default the z3 on PATH). The results
# go to CACHE/results/SUITE-TIME.csv; the summary counts solved instances (correct answer, model
# checked) and the PAR-2 score (seconds; an unsolved instance counts 2 * TIMEOUT).
# Exit code 1 when an answer is wrong or a model is bad.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
SUITE=${1:?usage: bench/run.sh SUITE [SOLVER]}
SOLVER=${2:-$ROOT/target/release/qfbv}
DIR=$ROOT/bench/$SUITE
[ -f "$DIR/suite.sh" ] || { echo "no suite $DIR/suite.sh" >&2; exit 2; }
[ -x "$SOLVER" ] || { echo "no solver $SOLVER (cargo build --release)" >&2; exit 2; }
# shellcheck source=/dev/null
. "$DIR/suite.sh"
JOBS=${BENCH_JOBS:-$JOBS}
Z3=${Z3:-$(command -v z3 || true)}
[ -n "$Z3" ] || { echo "z3 not found (set Z3)" >&2; exit 2; }
CACHE=${BENCH_CACHE:-$ROOT/bench/cache}
mkdir -p "$CACHE/results" "$CACHE/$SUITE"

# The archive.
ARCHIVE=$CACHE/$SOURCE_FILE
md5ok() { [ -f "$ARCHIVE" ] && echo "$SOURCE_MD5  $ARCHIVE" | md5sum -c --status; }
if ! md5ok; then
    echo "downloading $SOURCE_URL"
    curl -fL --retry 3 -o "$ARCHIVE.part" "$SOURCE_URL"
    mv "$ARCHIVE.part" "$ARCHIVE"
    md5ok || { echo "md5 of $ARCHIVE is not $SOURCE_MD5" >&2; exit 2; }
fi

# The instances: extract the ones missing or changed, then check every hash.
LIST=$CACHE/$SUITE/instances.sha256
grep -v '^\s*\(#\|$\)' <<<"$INSTANCES" | awk '{print $1 "  " $3}' >"$LIST"
grep -v '^\s*\(#\|$\)' <<<"$INSTANCES" | awk '{print $3}' >"$CACHE/$SUITE/paths"
if ! (cd "$CACHE/$SUITE" && sha256sum -c --status "$LIST" >/dev/null 2>&1); then
    echo "extracting $(wc -l <"$CACHE/$SUITE/paths") instances from $SOURCE_FILE"
    tar -I zstd -xf "$ARCHIVE" -C "$CACHE/$SUITE" -T "$CACHE/$SUITE/paths"
    (cd "$CACHE/$SUITE" && sha256sum -c --quiet "$LIST") || { echo "instance hashes differ" >&2; exit 2; }
fi
# The known answers of the suite are the :status of the files.
grep -v '^\s*\(#\|$\)' <<<"$INSTANCES" | while read -r _ st p; do
    grep -q "(set-info :status $st)" "$CACHE/$SUITE/$p" || { echo "status of $p is not $st" >&2; exit 2; }
done

OUT=$CACHE/results/$SUITE-$(date -u +%Y%m%dT%H%M%SZ).csv
echo "suite $SUITE: $(wc -l <"$CACHE/$SUITE/paths") instances, timeout ${TIMEOUT}s, memory ${MEM_GB}GB, $JOBS jobs"
set +e
python3 "$ROOT/frontend/tools/eval.py" "$SOLVER" "$Z3" "$OUT" --timeout "$TIMEOUT" --mem "$MEM_GB" \
    --jobs "$JOBS" $(sed "s|^|$CACHE/$SUITE/|" "$CACHE/$SUITE/paths")
CODE=$?
python3 - "$OUT" "$TIMEOUT" "$CACHE/$SUITE/" <<'EOF'
import csv, sys
out, timeout, prefix = sys.argv[1], float(sys.argv[2]), sys.argv[3]
rows = list(csv.DictReader(open(out)))
solved = [r for r in rows if r["answer"] == r["status"] and r["model"] in ("ok", "-")]
par2 = sum(float(r["seconds"]) if r in solved else 2 * timeout for r in rows)
for r in rows:
    mark = "solved" if r in solved else "-"
    print("%-8s %-7s %-7s %8s  %s" % (mark, r["status"], r["answer"], r["seconds"], r["file"][len(prefix):]))
print("solved %d of %d (sat %d, unsat %d), PAR-2 %.1f s" % (
    len(solved), len(rows), sum(r["status"] == "sat" for r in solved),
    sum(r["status"] == "unsat" for r in solved), par2))
bad = [r for r in rows if (r["answer"] in ("sat", "unsat") and r["answer"] != r["status"]) or r["model"] == "bad"]
sys.exit(1 if bad else 0)
EOF
SUM=$?
set -e
echo "results: $OUT"
[ "$CODE" = 0 ] && [ "$SUM" = 0 ]
