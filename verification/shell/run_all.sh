#!/usr/bin/env bash
# Run every machine check of paper/main.tex and compare the three
# implementations of closure_checks line by line.
#
#   verification/shell/run_all.sh            run what is installed
#   STRICT=1 verification/shell/run_all.sh   fail if a tool is missing
#
# Tools: python3, julia, a C99 compiler, lake (Lean 4), M2 (Macaulay2).
# MATHLIB=1 also builds verification/lean-mathlib (Lean 4 with Mathlib).
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

echo "== Fermat fourfolds of degree prime to 6"
python3 "$V/python/fermat_fourfolds.py" 55 > "$OUT/ffpy.txt"
echo "ok    Python: $(tail -1 "$OUT/ffpy.txt")"
ffsame() {  # ffsame <name> <file>: compare with the Python output for m <= 55
    if diff -q "$OUT/ffpy.txt" "$2" >/dev/null; then
        echo "ok    $1 output is identical to Python (m <= 55)"
    else
        echo "FAIL  $1 output differs from Python"; diff "$OUT/ffpy.txt" "$2" | head; status=1
    fi
}
if have julia; then
    julia "$V/julia/fermat_fourfolds.jl" 55 > "$OUT/ffjl.txt"; ffsame Julia "$OUT/ffjl.txt"
else missing julia; fi
if have "$CC"; then
    "$CC" -std=c99 -O2 -Wall -Wextra -Werror -o "$OUT/ff" "$V/c/fermat_fourfolds.c"
    "$OUT/ff" 55 > "$OUT/ffc.txt"; ffsame C "$OUT/ffc.txt"
    "$OUT/ff" 125 > "$OUT/ffc125.txt"
    if diff -q "$OUT/ffc125.txt" "$V/c/fermat_fourfolds_125.expected" >/dev/null; then
        echo "ok    C: classification holds for every m <= 125 prime to 6, output as stored"
    else echo "FAIL  C output for m <= 125 differs from the stored copy"; status=1; fi
else missing "$CC"; fi

echo "== Fermat fourfolds of odd degree divisible by 3"
python3 "$V/python/fermat_odd.py" 63 > "$OUT/fopy.txt"
echo "ok    Python: $(tail -1 "$OUT/fopy.txt")"
fosame() {  # fosame <name> <file>: compare with the Python output for m <= 63
    if diff -q "$OUT/fopy.txt" "$2" >/dev/null; then
        echo "ok    $1 output is identical to Python (m <= 63)"
    else
        echo "FAIL  $1 output differs from Python"; diff "$OUT/fopy.txt" "$2" | head; status=1
    fi
}
if have julia; then
    julia "$V/julia/fermat_odd.jl" 63 > "$OUT/fojl.txt"; fosame Julia "$OUT/fojl.txt"
else missing julia; fi
if have "$CC"; then
    "$CC" -std=c99 -O2 -Wall -Wextra -Werror -o "$OUT/fo" "$V/c/fermat_odd.c"
    "$OUT/fo" 63 > "$OUT/foc.txt"; fosame C "$OUT/foc.txt"
    "$OUT/fo" 105 > "$OUT/foc105.txt"
    if diff -q "$OUT/foc105.txt" "$V/c/fermat_odd_105.expected" >/dev/null; then
        echo "ok    C: every generating Hodge sextuple without a pair has a move or is exceptional, m <= 105"
    else echo "FAIL  C output for m <= 105 differs from the stored copy"; status=1; fi
else missing "$CC"; fi

echo "== Fermat varieties of degree 114"
python3 "$V/python/fermat114.py" > "$OUT/f114py.txt"
echo "ok    Python: $(tail -1 "$OUT/f114py.txt")"
python3 "$V/python/fermat114.py" --common > "$OUT/f114pyc.txt"
if have julia; then
    julia "$V/julia/fermat114.jl" > "$OUT/f114jl.txt"
    if diff -q "$OUT/f114py.txt" "$OUT/f114jl.txt" >/dev/null; then
        echo "ok    Julia output is identical to Python (exact family I residues included)"
    else echo "FAIL  Julia output differs from Python"; status=1; fi
else missing julia; fi
if have "$CC"; then
    "$CC" -std=c99 -O2 -Wall -Wextra -Werror -o "$OUT/f114" "$V/c/fermat114.c"
    "$OUT/f114" > "$OUT/f114c.txt"
    if diff -q "$OUT/f114pyc.txt" "$OUT/f114c.txt" >/dev/null; then
        echo "ok    C output is identical to Python (characters, nu_19, exponent conditions)"
    else echo "FAIL  C output differs from Python"; status=1; fi
else missing "$CC"; fi
if python3 -c "import flint" 2>/dev/null; then
    python3 "$V/python/fermat114.py" --lattice | grep -q "B = S + Z u(beta)" \
        && echo "ok    lattices: [B_57 : S_57] = 2 and B_114 = S_114 + Z u(beta)" \
        || { echo "FAIL  lattice check"; status=1; }
    python3 "$V/python/family2_certificate.py" > "$OUT/cert.txt" 2>&1 && grep -q "ALL CHECKS PASSED" "$OUT/cert.txt" \
        && echo "ok    family II: interval certificate passed ($(grep '(3) I' "$OUT/cert.txt" | sed 's/^ *//'))" \
        || { echo "FAIL  family II certificate"; cat "$OUT/cert.txt"; status=1; }
    FAMILY2_PREC=600 python3 "$V/python/family2_certificate.py" > "$OUT/cert600.txt" 2>&1 \
        && grep -q "ALL CHECKS PASSED" "$OUT/cert600.txt" \
        && echo "ok    family II: the certificate also passes at 600 bits" \
        || { echo "FAIL  family II certificate at 600 bits"; cat "$OUT/cert600.txt"; status=1; }
else missing python-flint; fi
if python3 -c "import sympy" 2>/dev/null; then
    python3 "$V/python/family1_symbolic.py" | grep -q "closed formula confirmed" \
        && echo "ok    family I: closed formula for I(lambda) confirmed symbolically" \
        || { echo "FAIL  family I symbolic check"; status=1; }
else missing sympy; fi

echo "== Lean"
if have lake; then
    (cd "$V/lean" && lake build > "$OUT/lean.txt" 2>&1) || { cat "$OUT/lean.txt"; status=1; }
    if grep -q "sorryAx" "$OUT/lean.txt"; then echo "FAIL  Lean uses sorry"; status=1; fi
    if grep -q "ofReduceBool" "$OUT/lean.txt" || grep -qE "by[[:space:]]+native_decide" "$V/lean/Closure.lean"; then
        echo "FAIL  Lean uses native_decide"; status=1; fi
    n=$(grep -c "depends on axioms\|does not depend on any axioms" "$OUT/lean.txt" || true)
    if [ "$n" = 20 ]; then echo "ok    Lean: Closure builds, 20 theorems report standard axioms only"
    else echo "FAIL  Lean: expected 20 axiom reports, found $n"; status=1; fi
else missing lake; fi

echo "== Lean with Mathlib (set MATHLIB=1; downloads Mathlib on first use)"
if [ "${MATHLIB:-0}" = 1 ]; then
    if have lake; then
        (cd "$V/lean-mathlib" && lake exe cache get > "$OUT/mlc.txt" 2>&1 && lake build > "$OUT/ml.txt" 2>&1 \
            && lake env lean Axioms.lean > "$OUT/mlax.txt" 2>&1) || { tail -20 "$OUT/ml.txt"; status=1; }
        if grep -rqE "\bsorry\b|native_decide" "$V/lean-mathlib/FermatHodge"; then
            echo "FAIL  FermatHodge uses sorry or native_decide"; status=1; fi
        if grep -q "sorryAx" "$OUT/mlax.txt"; then echo "FAIL  FermatHodge depends on sorryAx"; status=1; fi
        n=$(grep -cE "depends on axioms: \[(propext|Classical.choice|Quot.sound|, )*\]|does not depend on any axioms" "$OUT/mlax.txt" || true)
        if [ "$n" = 18 ]; then echo "ok    Lean+Mathlib: FermatHodge builds, 18 main theorems use the standard axioms only"
        else echo "FAIL  Lean+Mathlib axiom check"; cat "$OUT/mlax.txt"; status=1; fi
    else missing lake; fi
else echo "skip  MATHLIB is not set"; fi

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
