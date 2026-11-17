# A minimal suite: 20 small QF_BV instances of the SMT-LIB 2025 release (Zenodo record 16740866,
# non-incremental/QF_BV), kept here at their paths in that release, each with its source and license
# in its header. Chosen among the smallest instances with a known status that the solver answered
# within 10 s, spread over their families (17 sat, 3 unsat). Answers are checked against the
# status; models are not checked.
DESCRIPTION="SMT-LIB 2025 QF_BV, 20 small instances (17 sat, 3 unsat)"
TIMEOUT=10
MEMORY_MB=2048
fetch() { cp -r "$(dirname "$SUITE_SH")/instances/." "$1/"; cp "$(dirname "$SUITE_SH")/expected" "$1/expected"; }
