#!/usr/bin/env bash
# Run every machine check of paper/main.tex and compare the three
# implementations of closure_checks line by line.
#
#   verification/shell/run_all.sh            run what is installed
#   STRICT=1 verification/shell/run_all.sh   fail if a tool is missing
#
# Tools: python3, julia, a C99 compiler, lake (Lean 4), M2 (Macaulay2).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
V="$ROOT/verification"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
STRICT="${STRICT:-0}"
status=0

have() { command -v "$1" >/dev/null 2>&1; }
missing() {
    if [ "$STRICT" = 1 ]; then echo "FAIL  $1 is not installed"; status=1
    else echo "skip  $1 is not installed"; fi
}
same() {  # same <name> <file>: compare with the Python output
    if diff -q "$OUT/py.txt" "$2" >/dev/null; then
        echo "ok    $1 output is identical to Python"
    else
        echo "FAIL  $1 output differs from Python"; diff "$OUT/py.txt" "$2" | head; status=1
    fi
}

echo "== closure checks"
python3 "$V/python/closure_checks.py" > "$OUT/py.txt"
echo "ok    Python: $(tail -1 "$OUT/py.txt")"
if diff -q <(grep -v '^$' "$OUT/py.txt" | grep -v 'lines, all checks passed') \
           "$V/expected_output.txt" >/dev/null; then
    echo "ok    Python output matches verification/expected_output.txt"
else
    echo "FAIL  Python output differs from verification/expected_output.txt"; status=1
fi

if have julia; then
    julia "$V/julia/closure_checks.jl" > "$OUT/jl.txt"; same Julia "$OUT/jl.txt"
else missing julia; fi

CC="${CC:-cc}"
if have "$CC"; then
    "$CC" -std=c99 -O2 -Wall -Wextra -Werror -o "$OUT/cc" "$V/c/closure_checks.c"
    "$OUT/cc" > "$OUT/c.txt"; same C "$OUT/c.txt"
else missing "$CC"; fi

echo "== Lean"
if have lake; then
    (cd "$V/lean" && lake build > "$OUT/lean.txt" 2>&1) || { cat "$OUT/lean.txt"; status=1; }
    if grep -q "sorryAx" "$OUT/lean.txt"; then echo "FAIL  Lean uses sorry"; status=1; fi
    if grep -q "ofReduceBool" "$OUT/lean.txt" || grep -qE "by[[:space:]]+native_decide" "$V/lean/Closure.lean"; then
        echo "FAIL  Lean uses native_decide"; status=1; fi
    n=$(grep -c "depends on axioms\|does not depend on any axioms" "$OUT/lean.txt" || true)
    echo "ok    Lean: Closure builds, $n theorems report standard axioms only"
else missing lake; fi

echo "== Macaulay2"
if have M2; then
    M2 --script "$V/m2/fermat_jacobian.m2" > "$OUT/m2f.txt"
    bad=0
    while read -r line; do
        [ -z "$line" ] && continue
        grep -qxF "$line" "$OUT/py.txt" || { echo "FAIL  M2 line not in Python output: $line"; bad=1; }
    done < "$OUT/m2f.txt"
    [ "$bad" = 0 ] && echo "ok    M2 Jacobian-ring Hodge numbers agree with the character counts ($(grep -c . "$OUT/m2f.txt") lines)" || status=1
    M2 --script "$V/m2/max_noether.m2" > "$OUT/m2n.txt"
    if diff -q "$OUT/m2n.txt" "$V/m2/max_noether.expected" >/dev/null; then
        echo "ok    M2 Max Noether: dim I_2 = (g-2)(g-3)/2 for g = 3, 6, 10, 15, 21"
    else echo "FAIL  M2 Max Noether output changed"; status=1; fi
else missing M2; fi

echo
if [ "$status" = 0 ]; then echo "all checks passed"; else echo "SOME CHECKS FAILED"; fi
exit "$status"
