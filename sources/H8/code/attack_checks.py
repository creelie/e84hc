#!/usr/bin/env python3
"""
attack_checks.py

The attack scripts as a verification item.  Item (LV).

The scripts in attack/ run four tracks on the inputs that the closure graph leaves
open, and an adversarial verifier re-implemented the central computations of
each track.  The track scripts, the verifiers' scripts and the unedited
transcripts of their runs are packaged in attack/, one subdirectory per
track, and attack/README.md states every claim in the corrected form the
verifiers gave it, says which claims are proved, which are computed and
which are conditional, and gives the run time of every script.  Nothing
proved or computed there is a new unconditional case of the Hodge
conjecture.

This script runs a fast subset of the packaged scripts, each in its own
subprocess with bytecode writing switched off (python3 -B), reads the numbers
they print and turns them into checks.  Where a script is run on part of its
cases only, a short driver imports it and calls its own functions.  The
long runs are not repeated here; their transcripts are in
attack/*/transcripts/.

  (A) quartic_cm/, track T1, the Weil classes W_F of a quartic CM field F at
      n = 2 (the scripts write T for the space the paper calls R_F).  At a
      member with Hodge group Res_{F0/Q} SU(V,H) the Hodge
      classes in H^2 and H^4 have dimensions 2 and 7, and W_F meets the
      products of divisor classes in 0 (t1_generic.py, two of its six
      (field, H) pairs).  The F-semilinear phi on T = wedge^2_F H^1 with
      q(x,y) = h(x, phi y) has phi^2 = (det H)^{-1}, the commutant of
      su(V,H) on T is F + F phi, and the Casimir class C_q lies in the span
      of the pull-backs of W_F (t1_T.py on one pair; the verifier's
      v_phi.py with a non-diagonal H).  The criterion numbers: dim HT^2 =
      120, r = 80 for a pure Weil class with annihilator 0 + 16 + 24,
      r = 112 for a generic corrected character with the 8-dimensional
      tangent space as annihilator, and r >= 68 for every shape
      (t1_annihilator.py, t1_lowerbound.py, t1_fullflat.py; the verifier's
      v_ann.py, v_fullflat.py), and the binomial shapes of rank 92 and 96
      that the verifier added (v_binomial_9296.py).
  (B) mumford_target/, track T2, the Mumford fourfold X.  The multiplicities
      1, 6, 16, 24, 16, 6, 1 of T = Lie(G) in H^*(X x X), none in H^*(X),
      and the Hodge numbers (1,7,1) (t2_weights.py; the verifier's
      v1_weights.py).  Pull-backs and products of Hodge classes of X x X
      span 7 of the 8 dimensions of (V^(x)4)^G and miss the hyperdeterminant
      class Det; composites of two correspondences reach it (the verifier's
      v2_pullbacks.py).  The Schur-Weyl numbers 8 and 125 (v4_schurweyl.py),
      and the zero-sum property at the CM points (v3_cm_hilbert.py).
  (C) explicit_objects/, track T3, the split member X x X^ with
      K = Q(sqrt(-d)).  The Hochschild profile (1, 2n, 2C(n,2), ...,
      2C(n,n-1), 1) of a secant class and chi(F,F) (t3_verify.py; the
      verifier's v8_xprofile.py at other d); the n = 2 certificate numbers
      (1,8,18,8,1), r(ch E) = 18, R = 3/4 and the n = 3 certificate numbers
      (t3_verify.py; v2_orlov.py, v9_rG.py, v3_symbolic.py, v10_locus.py);
      the n = 4 count 88; the parity numbers of S^2(E[1]) (x) P, rank 3 and
      r = 23 (t3_verify.py; v6_sym2.py); and the erratum to ex:splitsmall at
      n = 3 (v5_exsplit.py).
  (D) natural_objects/, track T4, the split member at n = 4.  dim T = 16 and
      rank(T _| ch F) = 6 for the natural objects off C_theta, exactly over
      Q(i) (the verifier's v3_tspace.py) and modulo p with r(gamma) = 56,
      72, 88, 104 (t4_contr.py); the Hodge ring of dimension 55, the
      relation sum m_i [B_i] = 14 W2 and the configurations of the minimal
      support theorem (the verifier's v1_relations.py); the index 2612736000
      of the lattice of subtorus classes and its intersection with the Weil
      plane (t4_sublattice.py; v2_lattice.py); the least relation over the
      12870 eight-sets (v4_search.py); the intersection numbers of the
      explicit example (v5_chi.py); and the cross-check with the paper's
      exhaustive n = 2 search of item (XIII), here on the box of size 2
      (t4_n2_cross.py 2; the box of size 3, about four minutes, is in
      attack/natural_objects/transcripts/n2_cross.log).

Run with

    python3 -B attack_checks.py

from the directory containing it, or with its path from any other.  It takes
about two and a half minutes on one core; the last line is 'N checks passed,
M failed', and the exit status is nonzero if a check fails.
"""

import os
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
ATTACK = os.path.join(HERE, "attack")
TIMEOUT = 900

PASS, FAIL = [], []
RUNS = []


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    (PASS if ok else FAIL).append(name)
    print("    [%s] %s" % (tag, name))
    if detail:
        for line in detail.split("\n"):
            print("           " + line)


def run(where, *argv, code=None, label=None):
    """Run a packaged script, or a short driver importing one, with
    attack/<where> as working directory; return (stdout, exit status)."""
    cmd = [sys.executable, "-B"] + (["-c", code] if code is not None
                                    else list(argv))
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    name = "%s/%s" % (where, label if label else " ".join(argv))
    t0 = time.time()
    try:
        res = subprocess.run(cmd, cwd=os.path.join(ATTACK, where),
                             capture_output=True, text=True, env=env,
                             timeout=TIMEOUT)
        out, status = res.stdout, res.returncode
    except (subprocess.TimeoutExpired, OSError) as exc:
        out, status = "", type(exc).__name__
    dt = time.time() - t0
    RUNS.append((name, dt))
    print("  ran %s  (%.1f s, exit status %s)" % (name, dt, status))
    return out, status


def summary_ok(out, status, npass):
    """The script exited normally and reports npass checks, none failed."""
    m = re.search(r"(\d+) checks passed, (\d+) failed", out)
    return (status == 0 and m is not None and int(m.group(1)) == npass
            and int(m.group(2)) == 0)


def count(pattern, out):
    return len(re.findall(pattern, out))


def lines_with(out, *needles):
    return [ln for ln in out.splitlines() if all(s in ln for s in needles)]


# ---------------------------------------------------------------- (A) T1

def track_T1():
    print("  (A) quartic_cm/: W(F,2,delta) for a quartic CM field F")
    w = "quartic_cm"

    drv = ("import sys\n"
           "from fractions import Fraction as Fr\n"
           "import t1_generic as G\n"
           "G.run_field(5, Fr(5, 2), Fr(1, 2), 'Q(zeta_5)', [(1, 0, 1), "
           "(1, 0, 1), (1, 0, -1), (3, 0, -1)], '1,1,-1,-3')\n"
           "G.run_field(2, 3, 1, 'Q(sqrt(-(3+sqrt2)))', [(1, 0, 1), "
           "(2, 1, 1), (1, 0, -1), (3, 1, -1)], '1,2+s,-1,-(3+s)')\n"
           "sys.exit(0 if G.summary() else 1)\n")
    out, st = run(w, code=drv, label="t1_generic.py (two pairs)")
    nul = [int(x) for x in re.findall(r"nullity mod p = (\d+)", out)]
    check("t1_generic.py on Q(zeta_5) with H = diag(1,1,-1,-3) and on the "
          "non-Galois Q(sqrt(-(3+sqrt2))) with H = diag(1,2+s,-1,-(3+s)): "
          "su(V,H) has Q-dimension 30, W_F has Q-dimension 4 and is killed "
          "by su(V,H); 20 checks passed, 0 failed",
          summary_ok(out, st, 20) and count(r"found 30\b", out) == 2
          and count(r"\[PASS\] dim_Q su\(V,H\) = 30", out) == 2
          and count(r"\[PASS\] dim_Q W_F = 4", out) == 2
          and count(r"\[PASS\] W_F killed by su\(V,H\)", out) == 2)
    check("Hodge classes in H^2: exactly 2 at a member with Hodge group "
          "Res SU(V,H) (two explicit invariants, nullity mod p 2 as the "
          "upper bound), for both pairs",
          nul[0::2] == [2, 2] and count(
              r"\[PASS\] P_1, P_s invariant and independent", out) == 2,
          "nullities mod p (wedge^2, wedge^4, per pair): %s" % nul)
    check("Hodge classes in H^4: exactly 7 = 3 products of divisor classes "
          "+ 4 Weil classes (explicit rank 7, nullity mod p 7), and W_F "
          "meets the products in 0, for both pairs",
          nul[1::2] == [7, 7] and len(nul) == 4 and count(
              r"\[PASS\] explicit invariants in wedge\^4: 3 products \+ 4 "
              r"Weil, rank 7", out) == 2 and count(
              r"\[PASS\] W_F meets Lefschetz products in 0", out) == 2)

    drv = ("import sys\n"
           "from fractions import Fraction as Fr\n"
           "import t1_T as T\n"
           "T.run(5, Fr(5, 2), Fr(1, 2), 'Q(zeta_5)', [(1, 0, 1), (1, 0, 1), "
           "(1, 0, -1), (3, 0, -1)], '1,1,-1,-3')\n"
           "sys.exit(0 if T.summary() else 1)\n")
    out, st = run(w, code=drv, label="t1_T.py (one pair)")
    check("t1_T.py on Q(zeta_5), H = diag(1,1,-1,-3), det H = 3: phi is "
          "F-semilinear, q(x,y) = h(x, phi y), phi^2 = (det H)^{-1}, and "
          "phi commutes with wedge^2 su(V,H)",
          summary_ok(out, st, 8)
          and "det H = (Fraction(3, 1), Fraction(0, 1), Fraction(0, 1), "
              "Fraction(0, 1))" in out
          and count(r"\[PASS\] phi is F-semilinear, q\(x,y\) = h\(x, phi y\),"
                    r" phi\^2 = 1/det H", out) == 1
          and count(r"\[PASS\] phi commutes with wedge\^2 su\(V,H\)", out) == 1)
    check("the commutant of su(V,H) on T = Q^24 is F + F phi: 8 independent "
          "commuting maps, nullity mod p 8",
          "nullity mod p = 8" in out and count(
              r"\[PASS\] F \+ F phi: 8 independent", out) == 1)
    check("the Casimir class: Delta^* C_q = 6 w(c), C_q is killed by the "
          "diagonal su(V,H) and lies in the 20-dimensional Q-span of the "
          "pull-backs f_{a,b}^* W_F",
          "rank 20, with C_q 20" in out
          and count(r"\[PASS\] Delta\^\* C_q = 6 \* \(Weil class of c\)",
                    out) == 1
          and count(r"\[PASS\] C_q is killed by the diagonal", out) == 1)

    out, st = run(w + "/verify", "v_phi.py")
    check("the verifier's v_phi.py, over Q(zeta_5) in F-coordinates with a "
          "non-diagonal H: phi^2 = (det H)^{-1}; for g in U(V,H) with det g "
          "not in Q, phi g = conj(det g) g phi, so phi commutes with SU(V,H) "
          "but not with U(V,H)",
          st == 0
          and "phi^2 = (det H)^{-1} * id  (non-diagonal H): True" in out
          and "det g in Q: False" in out
          and "phi o g = conj(det g) g o phi on T: True" in out
          and "phi commutes with wedge^2 of su(V,H) element: True" in out)

    out, st = run(w, "t1_annihilator.py")
    check("t1_annihilator.py: dim HT^2 = 120 = 28 + 64 + 28, and a pure "
          "Weil class has r = 80 with annihilator 0 + 16 + 24 (the "
          "F-linear first-order deformations and the bivectors mixing two "
          "embeddings); 5 checks passed, 0 failed",
          summary_ok(out, st, 5) and "HT^2 dimension: 120" in out
          and "r = 80, dim Ann = 40, by summand {'z': 0, 'v': 16, 'pi': 24}"
          in out)
    check("t1_annihilator.py: r = 112 for three generic gamma = omega + "
          "p(theta_1, theta_2) and three with p in the single polarisation, "
          "the annihilator being the 8-dimensional tangent space, in H^1(T)",
          count(r"r = 112, dim Ann = 8, \{'z': 0, 'v': 8, 'pi': 0\}",
                out) == 6)

    out, st = run(w + "/verify", "v_ann.py")
    v80 = lines_with(out, "pure omega cs=", "r = 80",
                     "{'z': 0, 'v': 16, 'pi': 24}")
    check("the verifier's v_ann.py, a separate model: dim HT^2 = 120, and "
          "r = 80 with annihilator 0 + 16 + 24 for four coefficient vectors "
          "of omega",
          st == 0 and "dim HT^2 = 120" in out and len(v80) == 4)
    check("v_ann.py: the F-linear tangent space preserving theta_0 and "
          "theta_1 has dimension 8 and kills three generic gamma, which have "
          "r = 112; the monomial shapes give r in {80, 84, 88, 104, 108, 112}",
          "tangent space (F-linear, preserving theta_0, theta_1): dim 8"
          in out and count(r"generic gamma: r = 112 ; 8-dim tangent space "
                           r"kills gamma: True", out) == 3
          and "set of values: [80, 84, 88, 104, 108, 112]" in out)
    lb = [int(x) for x in re.findall(
        r"p-independent lower bound \(cs=[^)]*\): (\d+)", out)]
    out2, st2 = run(w, "t1_lowerbound.py")
    lb2 = re.findall(r"rank of the p-independent part of the contraction: "
                     r"(\d+)", out2)
    check("r(gamma) >= 68 for every p: the rank of the p-independent part of "
          "the contraction is 68 in t1_lowerbound.py, and 68 for two "
          "coefficient vectors of omega in v_ann.py, whose p-support is "
          "exactly the 256 products of the eight pairs",
          st2 == 0 and lb2 == ["68"] and lb == [68, 68]
          and "p-support monomials: 256 (from THP: 256, equal: True)" in out)

    out, st = run(w, "t1_fullflat.py")
    out2, st2 = run(w + "/verify", "v_fullflat.py")
    check("a general flat Hodge class with nonzero Weil part has r = 112: "
          "three trials in t1_fullflat.py and three in the verifier's "
          "v_fullflat.py",
          summary_ok(out, st, 1) and count(r"general flat gamma: r = 112",
                                           out) == 3
          and st2 == 0 and count(r"general flat gamma: r = 112", out2) == 3)

    out, st = run(w + "/verify", "v_binomial_9296.py")
    pairs = re.findall(r"^\((\d), (\d)\) \((\d), (\d)\) (\d+)$", out, re.M)
    vals = {}
    for a, b, c, e, r in pairs:
        vals[((int(a), int(b)), (int(c), int(e)))] = int(r)
    check("binomial shapes of rank 92 and 96 (the verifier's correction of "
          "the list of values): 12 of the 300 pairs of monomials give 92 or "
          "96, among them r(omega + theta_1 + theta_0^2) = 92 and "
          "r(omega + theta_0^2 + theta_1^2) = 96, also for a second omega",
          st == 0 and len(vals) == 12 and set(vals.values()) == {92, 96}
          and vals.get(((0, 1), (2, 0))) == 92
          and vals.get(((0, 2), (2, 0))) == 96
          and "generic omega coeffs: 96 92" in out)


# ---------------------------------------------------------------- (B) T2

def track_T2():
    print("  (B) mumford_target/: the Mumford fourfold and the Kuga-Satake "
          "class")
    w = "mumford_target"
    mult = "[0, 0, 1, 0, 6, 0, 16, 0, 24, 0, 16, 0, 6, 0, 1, 0, 0]"

    out, st = run(w, "t2_weights.py")
    check("t2_weights.py: no V(2,0,0)-type summand in any wedge^k V, so T "
          "occurs in no H^k(X)(j); T occurs in H^n(X x X), n = 0..16, with "
          "multiplicities %s; 7 checks passed, 0 failed" % mult,
          summary_ok(out, st, 7)
          and "PASS no V(2,0,0)-type summand in any wedge^k V" in out
          and ("multiplicity of T_1 = V(2,0,0) in H^n(X x X), n = 0..16: "
               + mult) in out)
    check("the 12-dimensional unitary Hodge structure of weight one: the "
          "character-trivial part of its wedge^2 is T_1 + T_2 + T_3 plus 3 "
          "trivial summands, and T has Hodge numbers (1,7,1) there (the "
          "Hodge-theoretic attainment of the bound dim >= 6)",
          "-> T: {2: 1, 1: 7, 0: 1}" in out
          and "PASS it is T_1 + T_2 + T_3 + 3 copies of the trivial "
              "representation" in out
          and "PASS T inside H^2(Z) has Hodge numbers (1,7,1)" in out)

    out, st = run(w + "/verify", "v1_weights.py")
    check("the verifier's v1_weights.py, by the Weyl alternating-sum "
          "formula: the same multiplicities, the copy of T in H^2(X x X) "
          "lies in H^1 (x) H^1 and has Hodge numbers (1,7,1); 11 checks "
          "passed, 0 failed",
          summary_ok(out, st, 11)
          and ("(b) multiplicity of V(2,0,0) in H^n(X x X), n = 0..16: "
               + mult) in out
          and "(d) Hodge numbers (p=2,1,0) of T in H^1 (x) H^1: 1 7 1" in out
          and "PASS (b) the copy in H^2 is in H^1 (x) H^1" in out)

    out, st = run(w + "/verify", "v2_pullbacks.py")
    check("the verifier's v2_pullbacks.py, exact, in the exterior algebras "
          "of X^m: the Hodge classes of X x X of degree 4 have dimensions "
          "1, 1, 4, 1, 1 in the Kunneth components, and dim (V^(x)4)^G = 8",
          "(1) dim (wedge^a V (x) wedge^{4-a} V)^G, a=0..4: [1, 1, 4, 1, 1]"
          in out and "dim (V^(x)4)^G = 8" in out)
    check("pull-backs along integer homomorphisms X^4 -> X^2 and products "
          "of pulled-back divisor classes span exactly 7 of the 8 "
          "dimensions; the hyperdeterminant class Det, with Det(x,x,x,x) = "
          "6 Cayley(x), is not in that span",
          "exact rank of their span: 7" in out
          and "PASS (4) Det is NOT in the span of (3) (exact)" in out
          and "(4) Det(x,x,x,x)/Cayley(x) on random x: {Fraction(6, 1)}"
          in out)
    check("composites of two correspondences in that span reach Det: with "
          "them the span is all 8 dimensions, and one single composite has "
          "nonzero Det component; 10 checks passed, 0 failed",
          summary_ok(out, st, 10)
          and "(5) exact rank of span of T4_0 and all composites u o t "
              "(t,u in T4_0): 8" in out
          and "PASS (5) some single composite has nonzero hyperdeterminant "
              "component (exact)" in out)

    out, st = run(w + "/verify", "v4_schurweyl.py")
    check("the verifier's v4_schurweyl.py: E(x)F + F(x)E + H(x)H/2 = P - I/2, "
          "so s_k = Cas_k + 1/2; Q[S_2], Q[S_3], Q[S_4] act through algebras "
          "of dimension 2, 5, 14, so dim End_G(V (x) V) = 8 and "
          "dim End_G(V^(x)3) = 125; the SL2-invariants of (Q^2)^(x)6 have "
          "dimension 5 and are spanned by the S_6-orbit of eps^(x)3",
          summary_ok(out, st, 7)
          and "PASS (a) E(x)F + F(x)E + H(x)H/2 = P - I/2" in out
          and all("(b) dim image of Q[S_%d] on (Q^2)^(x)%d: %d" % (k, k, v)
                  in out for k, v in ((2, 2), (3, 5), (4, 14)))
          and "dim End_G(V(x)V) = 2^3 = 8, dim End_G(V^(x)3) = 5^3 = 125"
          in out
          and "PASS (c) the S_6-orbit of eps^(x)3 spans the 5-dim invariant "
              "space" in out)

    out, st = run(w + "/verify", "v3_cm_hilbert.py")
    irr = re.findall(r"^\s+\(([01, ]+)\) support", out, re.M)
    sizes = sorted(sum(int(x) for x in v.split(",")) for v in irr)
    check("the CM points (the verifier's v3_cm_hilbert.py): the zero-sum "
          "multisets of the eight weights {+-1}^3 with multiplicities at "
          "most 5 have exactly 6 irreducible elements, the four pairs "
          "{w,-w} and two quadruples, none with a repeated weight",
          summary_ok(out, st, 4) and "irreducible elements: 6" in out
          and sizes == [2, 2, 2, 2, 4, 4],
          "sizes of the irreducible zero-sum sets: %s" % sizes)


# ---------------------------------------------------------------- (C) T3

def track_T3():
    print("  (C) explicit_objects/: explicit objects at a split member")
    w = "explicit_objects"

    out, st = run(w, "t3_verify.py")
    check("t3_verify.py: 56 checks passed, 0 failed",
          summary_ok(out, st, 56))
    prof = count(r"\[PASS\] n=[2-5]: r\^k_X\(v\) = \(1,2n,2C\(n,2\),\.\.\.,"
                 r"2C\(n,n-1\),1\) for 12 secant v", out)
    chis = count(r"\[PASS\] n=[2-6]: chi\(F,F\) = 2\^\{n-1\}", out)
    check("the Hochschild profile of a secant class v on X: the rank of "
          "HT^k(X) -> H^*(X), xi -> xi _| v, is (1, 2n, 2C(n,2), ..., "
          "2C(n,n-1), 1) for n = 2..5, and chi(F,F) = 2^{n-1} (-1)^{n/2} "
          "d^{n/2-1} (a^2 d + b^2) for n even, 0 for n odd, n = 2..6",
          prof == 4 and chis == 5)
    cert2 = count(r"\[PASS\] n=2 d=\d+ F=(I_p|O_C\(p\)): Hochschild profile "
                  r"of ch\(E\) = \(1,8,18,8,1\) = \(1,4,1\)\^2 = Ext profile; "
                  r"Weil part .* != 0; R = 3/4, c1=c3=0", out)
    check("the n = 2 certificate E = Phi(F [x] F^vee), F = O_C(p) for "
          "d = 1, 2, 3, 5 and F = I_p for d = 1: the Hochschild profile of "
          "ch(E) is (1,8,18,8,1), the Ext profile; the Weil part is nonzero, "
          "and R = 3/4 with c_1 = c_3 = 0", cert2 == 5)
    cert3 = count(r"\[PASS\] n=3 d=(2|6) F=i_\*L on Theta: Hochschild "
                  r"profile of ch\(E\) = \(1,6,6,1\)\^2 = "
                  r"\(1,12,48,74,48,12,1\)", out)
    line3 = count(r"\[PASS\] n=3 d=(2|6|30|42): L=\(2k\+1\)x - k theta on "
                  r"C\^\(2\): ch_2\(i_\*L\)=0, chi\(L\)=-d", out)
    check("the n = 3 certificate, d = k(k+1): ch(i_*L) = Theta - d pt for "
          "d = 2, 6, 30, 42, and the Hochschild profile of ch(E) is "
          "(1,6,6,1)^2 = (1,12,48,74,48,12,1) for d = 2, 6",
          cert3 == 2 and line3 == 4)
    n4 = count(r"\[PASS\] n=4 d=\d pair .*: r\(ch E\) = 88 = r0 r2 \+ r1 r1 "
               r"\+ r2 r0 = 12 \+ 64 \+ 12", out)
    check("n = 4: r(ch E) = 88 = 12 + 64 + 12 for three pairs, and the "
          "minimal profile (1,8,12,8,1) has chi = -2 while a secant chi is "
          "at least 8 (the no-go assumes Ext^{<0}(F_i,F_i) = 0)",
          n4 == 3 and count(r"\[PASS\] n=4: minimal profile \(1,8,12,8,1\) "
                            r"has chi = -2, secant chi >= 8", out) == 1)
    s2 = count(r"\[PASS\] n=2 d=[123]: S\^2\(E\[1\]\) \(x\) P untwisted, "
               r"flat, rank 3, Weil .*, r = 23 \(odd", out)
    check("parity: at n = 2, S^2(E[1]) (x) P is untwisted and flat, of "
          "rank 3, with r = 23, which is odd (d = 1, 2, 3, t3_verify.py)",
          s2 == 3)

    out, st = run(w + "/verify", "v8_xprofile.py")
    check("the verifier's v8_xprofile.py at d = 1, 7, 10, values the track "
          "did not use: the same profiles for n = 2..5 and the chi formula "
          "for n = 2..6",
          st == 0 and "MISMATCH" not in out
          and count(r"n=[2-5] profiles checked", out) == 4
          and count(r"n=[2-6] chi formula: True", out) == 5)

    out, st = run(w + "/verify", "v2_orlov.py", "2", "1,2,3,5,6,7,11", "prof")
    rows = [ln for ln in out.splitlines() if ln.startswith("n=2 d=")]
    same = [ln for ln in rows if "F1=(0, 1) F2=(0, 1)" in ln
            or "F1=(1, 0) F2=(1, 0)" in ln]
    check("the verifier's v2_orlov.py at n = 2, d = 1, 2, 3, 5, 6, 7, 11, "
          "five pairs each: ch(E) is not flat, ch(E) e^{ell/2} is, with "
          "rho = 2 and mu_{m+2} = -mu_m/(4d), and r(ch E) = 18",
          st == 0 and len(rows) == 35
          and all("flat(ch)=False flat(ch e^{l/2})=True" in ln
                  and "rho=2 rec(-1/4d)=True" in ln
                  and "r(chE)=18 " in ln for ln in rows))
    check("v2_orlov.py: for F1 = F2 the ratio is R = 3/4 with c_1 = c_3 = 0 "
          "(14 cases), and the profile of the certificate begins "
          "(1, 8, 18, 8) for all seven d",
          len(same) == 14 and all("c1=0 c3=0 R=3/4" in ln for ln in same)
          and count(r"profile=\[1, 8, 18, 8\]", out) == 7)

    out, st = run(w + "/verify", "v9_rG.py")
    got = re.findall(r"n=(\d) d=(\d+): r\(ch G\) for 3 pairs = \[(\d+), "
                     r"(\d+), (\d+)\] \(expected (\d+)\)", out)
    want = {"2": 18, "3": 48, "4": 88}
    check("the verifier's v9_rG.py: r(ch G) for G = F1 [x] F2^vee on X x X "
          "is 18 at n = 2, 48 at n = 3 and 88 at n = 4, at d = 1, 7, 13 "
          "(n = 2, 3) and d = 1, 5, 7 (n = 4): the Kunneth count that gives "
          "r(ch E) = 18 for every d",
          st == 0 and len(got) == 9
          and all(int(a) == int(b) == int(c) == int(e) == want[n]
                  for n, _, a, b, c, e in got))

    out, st = run(w + "/verify", "v3_symbolic.py")
    check("the verifier's v3_symbolic.py, over Q(d) with d a symbol, n = 2, "
          "3: for the four basis pairs ch(E) is not flat, ch(E) e^{ell/2} "
          "is, with mu_{m+2} = -mu_m/(4d); at n = 2, R = 3/4 with "
          "c_1 = c_3 = 0 for F1 = F2",
          st == 0 and count(r"n=[23]: all four basis pairs flat after "
                            r"e\^\{ell/2\}, not before, rho<=2 recursion, "
                            r"for d symbolic: True", out) == 2
          and count(r"c1 = 0, c3 = 0, R = 3/4", out) == 2)

    out, st = run(w + "/verify", "v10_locus.py")
    loc = re.findall(r"n=(\d) d=\d+ v=\(\d, \d\): dim Ann_\{H\^1\(T\)\}"
                     r"\(kappa_B\) = (\d+)", out)
    check("the verifier's v10_locus.py: the first-order Hodge locus of "
          "kappa_B among all complex tori has dimension 5 at n = 2 (the "
          "exceptional ratio) and 9 = n^2 at n = 3",
          st == 0 and len(loc) == 6
          and all(int(k) == (5 if n == "2" else 9) for n, k in loc))

    out, st = run(w + "/verify", "v6_sym2.py")
    rows = re.findall(r"n=(\d) d=(\d) (S|L)\^2\(E\[1\]\)\(x\)P: rank (-?\d+) "
                      r"flat True .*?r=(\d+)", out)
    ok = len(rows) == 12
    for n, d, kind, rk, r in rows:
        if n == "2" and kind == "S":
            ok = ok and (rk, r) == ("3", "23")
        elif n == "2":
            ok = ok and (rk, r) == ("1", "12")
        else:
            ok = ok and (rk, r) == ("0", "57")
    ok = ok and count(r"S\^2\(E\[1\]\)\(x\)P: rank 3 .*R=3/4 r=23", out) == 4
    ok = ok and count(r"n=2 d=\d L\^2\(E\[1\]\)\(x\)P: rank 1 flat True "
                      r"weil\(my norm\.\)=\(0,0\)", out) == 4
    check("the verifier's v6_sym2.py, d = 1, 2, 3, 7: S^2(E[1]) (x) P has "
          "rank 3, R = 3/4 after an eta-twist and r = 23; Lambda^2(E[1]) (x) P "
          "has rank 1, no Weil part and r = 12; at n = 3 both have rank 0 "
          "and r = 57", st == 0 and ok)

    out, st = run(w + "/verify", "v5_exsplit.py")
    ok = st == 0
    for d in (1, 2, 3):
        ok = ok and ("n=2 d=%d: paper omega1 in Weil plane: True; paper "
                     "omega2 in Weil plane: True" % d) in out
        ok = ok and ("n=3 d=%d: paper omega1 in Weil plane: %s; paper omega2 "
                     "in Weil plane: True; d*gamma*l^2 - gamma^3/3 in plane: "
                     "True" % (d, d == 1)) in out
    check("ex:splitsmall (the verifier's v5_exsplit.py): at n = 3 the "
          "formerly printed gamma ell^2 - gamma^3/3 lies in the Weil plane "
          "only for d = 1, while d gamma ell^2 - gamma^3/3 and "
          "gamma^2 ell - d ell^3/3 lie in it for d = 1, 2, 3; at n = 2 both "
          "formulas do", ok)


# ---------------------------------------------------------------- (D) T4

def track_T4():
    print("  (D) natural_objects/: natural objects at n = 4")
    w = "natural_objects"

    out, st = run(w + "/verify", "v3_tspace.py", "1")
    ranks = dict(re.findall(r"\(T3\) (.+?)\s+rank T _\| ch = (\d+)", out))
    natural = ["O(beta)", "O(beta+betahat-ell)", "O(2beta-betahat+3ell)",
               "[B_(1,0)]", "[B_(2,1)]", "[B_(3,-2)]", "[B_(1,1)] e^beta",
               "[B_(1,2)] e^eta"]
    check("the verifier's v3_tspace.py, exact over Q(i) at X = C^4/(Z^4 + "
          "iZ^4), d = 1: dim T = 16, and T kills eta, W1 and W2",
          st == 0 and "(T1) dim T = 16" in out
          and "(T2) rank T_|eta = 0, T_|W1 = 0, T_|W2 = 0" in out)
    check("rank(T -> H^*, v -> v _| ch F) = 6 for three line bundles, three "
          "subtori and two twisted subtori off C_theta, 0 for the point, "
          "O(eta) and O(-2 eta); joint rank 6 over the eight subtori of the "
          "example",
          all(ranks.get(k) == "6" for k in natural)
          and all(ranks.get(k) == "0" for k in ("point", "O(eta)",
                                                 "O(-2 eta)"))
          and "(T4) joint rank of v -> (v _| [B_i])_i over the 8 subtori of "
              "the example = 6" in out,
          "ranks: %s" % ", ".join("%s %s" % kv for kv in ranks.items()))

    out, st = run(w, "t4_contr.py", "1")
    ht = re.findall(r"\(K3/K5\) (.+?)\s+rank HT\^2_\|ch =\s+(\d+)\s+rank "
                    r"T_\|ch =\s+(\d+)", out)
    rg = re.findall(r"rho = (\d)\s+r\(gamma\) mod p =\s+(\d+)\s+formula "
                    r"\(4\+rho\)16-8 = (\d+)", out)
    check("t4_contr.py, modulo p (lower bounds, matched by the exact values "
          "above): dim T = 16; rank HT^2 _| ch F = 28 for the natural F, and "
          "rank T _| ch F = 6 off C_theta, 0 for O(eta)",
          st == 0 and "(K2) dim T (mod p) = 16" in out and len(ht) == 7
          and all(h == "28" for _, h, _ in ht)
          and all(t == ("0" if k == "O(eta)" else "6") for k, _, t in ht))
    check("r(gamma) = 56, 72, 88, 104 for corrected characters of Hankel "
          "rank rho = 0, 1, 2, 3, as (4 + rho) 16 - 8",
          len(rg) == 5 and all(int(a) == (4 + int(r)) * 16 - 8 == int(b)
                               for r, a, b in rg)
          and sorted({int(a) for _, a, _ in rg}) == [56, 72, 88, 104])

    out, st = run(w + "/verify", "v1_relations.py", "1")
    check("the verifier's v1_relations.py, d = 1: the Hodge ring H_A has "
          "dimensions 1, 3, 6, 10, 15, 10, 6, 3, 1 (total 55), and the Weil "
          "classes from the eigenspaces of M agree with W1, W2",
          st == 0 and "[1, 3, 6, 10, 15, 10, 6, 3, 1] total 55" in out
          and "rank{W1, W2, Re alpha_+, Im alpha_+} = 2 (expect 2)" in out)
    check("the explicit relation sum m_i [B_i] = 14 W2 over the eight "
          "subtori (p,q) = (1,+-3), (1,+-2), (2,+-1), (3,+-1), in the "
          "convention phi^* = -B^{-1}, and -14 W2 in the convention "
          "phi^* = +B^{-1}; the closed form of the m_i gives a pure Weil class "
          "on 12 of 12 random eight-sets",
          "sum m_i [B_i] == 14 W2 (W2 = Im(gamma - delta ell)^4/delta): True"
          in out and "sum m_i [B_i] == -14 W2: False" in out
          and "relation (sum, W1, W2) = [['1/14', '0', '1']]" in out
          and "pure Weil class on random 8-sets of subtori: 12/12" in out)
    r4 = re.findall(r"\(R4\) (.+?)\s+relation-with-Q\[theta\] / pure "
                    r"relation over 3 draws: (\[.*\])", out)
    good = [c for c, v in r4 if c.startswith("8 on conic")]
    bad = [c for c, v in r4 if not c.startswith("8 on conic")]
    check("the minimal support theorem on examples: eight points on one "
          "conic through l_W give a pure relation, while seven points, and "
          "the splits 4+4, 5+3, 6+2, 6+1+1, 7+1, 3+3+2 over several conics, "
          "and random sets of eight (four line bundles and four subtori, or "
          "eight line bundles) give none",
          len(good) == 2 and len(bad) == 11
          and all(v == "[(True, True), (True, True), (True, True)]"
                  for c, v in r4 if c in good)
          and all(v == "[(False, False), (False, False), (False, False)]"
                  for c, v in r4 if c in bad)
          and "(R4) 4 random line bundles + 4 subtori: relation over 3 "
              "draws: [False, False, False]" in out
          and "(R4) 8 random line bundles: relation over 3 draws: [False, "
              "False, False]" in out)

    out, st = run(w + "/verify", "v2_lattice.py")
    idx = re.findall(r"H=(\d+): rank 9, Smith invariants \[1, 1, 1, 2, 6, 6, "
                     r"120, 120, 2520\], index 2612736000", out)
    out2, st2 = run(w, "t4_sublattice.py", "1", "10")
    check("the lattice of subtorus classes has rank 9 and index 2612736000 "
          "= 2^12 3^6 5^3 7 in Z^9, with Smith invariants 1, 1, 1, 2, 6, 6, "
          "120, 120, 2520 for the boxes 6, 8, 10 (the verifier's "
          "v2_lattice.py) and index 2612736000 for the box 10 "
          "(t4_sublattice.py)",
          st == 0 and idx == ["6", "8", "10"] and st2 == 0
          and "Lambda_sub has rank 9 and index 2612736000" in out2
          and 2 ** 12 * 3 ** 6 * 5 ** 3 * 7 == 2612736000)
    inter = {"1": "[['3/2', '0'], ['0', '7/2']]",
             "2": "[['5/6', '0'], ['0', '35/6']]",
             "3": "[['5/4', '0'], ['0', '5/4']]"}
    check("it meets the Weil plane in Z(3/2 W1) + Z(7/2 W2) for d = 1, "
          "Z(5/6 W1) + Z(35/6 W2) for d = 2 and Z(5/4 W1) + Z(5/4 W2) for "
          "d = 3",
          all(len(lines_with(out, "d=%s: Lambda cap Weil plane basis" % d,
                             "in W=24w coords: %s ; members check True"
                             % v)) == 1 for d, v in inter.items())
          and "i.e. in terms of W1 = 24 w1, W2 = 24 w2: %s" % inter["1"]
          in out2)

    out, st = run(w + "/verify", "v4_search.py")
    best = "((1, -3), (1, -2), (1, 2), (1, 3), (2, -1), (2, 1), (3, -1), (3, 1))"
    check("over all 12870 eight-sets with |p|, |q| <= 3 (the verifier's "
          "v4_search.py) the least relation has sum m^2 = 1028 and "
          "sum |m| = 68, at the eight subtori of the explicit relation",
          st == 0 and "8-sets: 12870" in out
          and ("min sum m^2 = 1028 at " + best) in out
          and ("min sum |m| = 68 at " + best) in out)

    out, st = run(w + "/verify", "v5_chi.py")
    check("the intersection numbers of the explicit example (v5_chi.py), "
          "d = 1, 2: |int [B_i][B_j]| = |det|^8, int [B] eta^4 = "
          "4! (d p^2 + q^2)^4, int eta^8 = 8! d^4",
          st == 0 and count(r"\|int B_i B_j\| = \|det\|\^8: True ; int B "
                            r"eta\^4 = 4!\(dp\^2\+q\^2\)\^4: True ; int eta\^8"
                            r" = 8! d\^4: True", out) == 2)

    out, st = run(w, "t4_n2_cross.py", "2")
    rows = re.findall(r"n=2 d=(\d) \(box 2\): (\d+) Weil tuples, sizes "
                      r"\{4: (\d+)\}; all four Lagrangians off C_theta: "
                      r"(\d+); on a conic through l_W: (\d+); pure Weil "
                      r"character: (\d+)", out)
    ok = st == 0 and [r[0] for r in rows] == ["1", "2"]
    for d, n, n4, off, conic, pure in rows:
        ok = ok and int(n) > 0 and n == n4 == off and conic == pure
    check("the cross-check with the paper's exhaustive n = 2 search "
          "(semiregularity.signed_search, item (XIII)) on the box "
          "|a|, |b|, |c| <= 2, d = 1, 2: every signed tuple of at most four "
          "line bundles with flat character and nonzero Weil part has "
          "exactly four terms, all four Lagrangians off C_theta, and as "
          "many lie on a conic through l_W as have a pure Weil character",
          ok, "; ".join("d=%s: %s tuples, %s on a conic, %s pure"
                        % (r[0], r[1], r[4], r[5]) for r in rows))


# ---------------------------------------------------------------- (E) gaps
def track_gaps():
    print()
    print("  (E) gaps/: the three remaining inputs, attacked through their "
          "smallest cases")
    w = "gaps/quartic_obstruction"
    for script, n, what in (
            ("a1_secant.py", 49, "the secant space S(t,q) of a quartic field: "
             "it is rational of dimension 4, its Hochschild profile is "
             "(1, 8, 2 rho + 4 N_w) and chi = 4(N(q)a^2 + c^2 + Tr(qbar f^2)), "
             "in 49 cases"),
            ("a1_lattice.py", 2, "the integral classes of the F_0-Hodge ring: "
             "the saturation lies in the congruence lattice c = g mod d"),
            ("a1_Lgen.py", 10, "the congruence lattice is spanned by integral "
             "classes, for d_F = 5, 8, 13, 17, 40"),
            ("a1_lattice_general.py", 15, "the integral classes on the "
             "lattice O^2 + (d^-1)^2 are the congruence lattice, for "
             "d_F = 12, 24, 28, 40, 56"),
            ("a1_lattice_local.py", 11, "the local expansion behind "
             "lem:quarticlattice, with delta and the entries of V as symbols: "
             "the congruence lattice is integral at every prime and every "
             "integral class satisfies the congruence"),
            ("a1_rank2_arith.py", 15, "the rank-two arithmetic of "
             "prop:quarticother for every real quadratic field: "
             "N(x + 4y) = N(x) mod 4 with D a symbol, the parity at the "
             "ramified prime above 2, and the three conditions on m for "
             "squarefree D < 200000 leave only D = 2 and D = 5"),
            ("a1_flat.py", 59, "the twisted character of an Orlov product of "
             "F-secant objects is invariant under G_F, so a Hodge class on "
             "the whole (F,2,1)-family, with a nonzero Weil part"),
            ("a1_rkappa.py", 8, "r(kappa) = 100 exactly for a rank-one "
             "secant pair, from an exact annihilator over Q(i)"),
            ("a1_flat_general.py", 96, "the twisted character of an Orlov "
             "product is invariant under G_F, with a nonzero Weil part, for "
             "F0 = Q(sqrt 2), Q(sqrt 13), Q(sqrt 17), Q(sqrt 10) (product "
             "model) and Q(sqrt 3), Q(sqrt 7) (lattice O^2 + (d^-1)^2), two "
             "q each"),
            ("a1_rkappa_general.py", 12, "r(kappa) = r^2(v_1) + 64 + "
             "r^2(v_2) on five further pairs: 102 for a mixed pair, 100 and "
             "104 over Q(sqrt 2), and 88 and 94 for F = Q(sqrt 5, i) with a "
             "class of N_w = 2"),
            ("a1_theorem_check.py", 4, "the identities of the quartic "
             "obstruction on random integral classes: 20 | chi in rank one; "
             "adj V = mu lbar l^T, sigma_2 = mu^2 N(Delta) and "
             "chi^2 = 4 mu^2 N(Delta) mod 5 in rank two; strict inequality "
             "on the complex-secant classes")):
        out, st = run(w, script)
        check("%s (%s): %d checks passed, 0 failed" % (what, script, n),
              summary_ok(out, st, n))
    out, st = run(w, "a1_general.py", "sqrt10", "2", "12")
    check("Q(sqrt 10) (a1_general.py sqrt10 2 12): the exact scan of 1841 "
          "complex-secant planes finds no admissible character "
          "(chi, rank V, r^2) = (4,1,18) or (6,2,20)",
          st == 0 and "scanned 1841 complex-secant planes" in out
          and "ADMISSIBLE: 0" in out)
    out, st = run("gaps/sextic", "s1_profile.py")
    check("the count beyond degree four (s1_profile.py): the secant profiles "
          "of a sextic CM field are palindromic, r^2 = sum rho_j + "
          "4 sum N_jk, chi = (-4)^3 N(q) sum |w|^2 < 0, and a minimal "
          "object needs only -chi >= r^3 - 2 r^2 + 22; the quartic profile "
          "(1, 8, 2 rho + 4 N_w, 8, 1) is reproduced",
          summary_ok(out, st, 7))
    w = "gaps/orlov_growth"
    out, st = run(w, "lagrangian_check.py")
    check("flatness in every dimension (lagrangian_check.py): at n = 1 and "
          "n = 2, with d a symbol, the four images of e^{+-st} [x] e^{+-st} "
          "are the pure spinors e^{+-(s/2d) eta} and the Weil classes",
          st == 0 and "ALL four images are pure spinors" in out
          and out.rstrip().endswith("True"))
    out, st = run(w, "euler.py")
    check("the equality count (euler.py): chi(F,F) in closed form for "
          "n = 2..12, the Hochschild profile of a secant class and "
          "R_n = 6n^2 - 2n (n >= 3), R_2 = 18, for n = 2..12",
          st == 0 and "False" not in out
          and count(r"matches closed form: True", out) >= 11
          and count(r"check True", out) >= 11)
    out, st = run(w, "divisor_sheaves.py")
    check("sheaves on divisors in the Orlov template (divisor_sheaves.py): "
          "for n >= 5 an admissible profile with Ext^<0 = 0 meets chi(F,F); "
          "ch(G) = r i^*(S T_b), so no line bundle; the Ext groups of "
          "i_*(V|_Theta) are beta_k plus End_0 terms; at n = 5 "
          "chi(End G) = r^2 (32 d^2 - 20 d - 1)/6 exceeds chi(O_Theta) = 1",
          summary_ok(out, st, 19))
    w = "gaps/f3prime"
    out, st = run(w, "invariants.py")
    check("the orthogonal determinant (invariants.py): SO(t)- and "
          "O(t)-invariants of V^(x)j agree for j < t and differ by one at "
          "j = t, t = 3..8, and det is invariant and reflection-odd",
          summary_ok(out, st, 48))
    out, st = run(w, "closure_f3prime_mot.py")
    check("the closure graph with the rule (F3') => (M) added "
          "(closure_f3prime_mot.py): the five minimal sufficient sets are "
          "unchanged", summary_ok(out, st, 6))


def main():
    t0 = time.time()
    track_T1()
    track_T2()
    track_T3()
    track_T4()
    track_gaps()
    print("  run time %.0f s (the slowest: %s)" % (
        time.time() - t0, ", ".join("%s %.0f s" % r for r in sorted(
            RUNS, key=lambda r: -r[1])[:3])))


if __name__ == "__main__":
    print("(LV) the attack scripts: a fast subset of their "
          "computations")
    main()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
