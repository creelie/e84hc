#!/usr/bin/env python3
"""
mumford_routes.py

Item (XLIX) of COMPUTATIONS.md: which of the open routes to the
Mumford target are needed, computed rather than listed.

The Mumford target is the first case of (F2): the Hodge conjecture for
X_t x X_t at every point t of the Mumford curve C.  The paper proves a number
of implications into and out of it and leaves a number of statements open.
This script carries that part of the logical skeleton as data, in the manner
of item (XXXIII): statements, each marked proved here or open, and Horn rules,
each of which is one theorem of the paper and carries its label.  Unlike the
rule set of item (XXXIII) this one contains equivalences, that is cycles, and
the forward closure is still reached by iterating the one step map to a fixed
point.

Statements:

  TARGET  the Hodge conjecture for X_t x X_t for every t in C
  UNCOUNT an exceptional class is algebraic at uncountably many t
  B_WW    the Lefschetz standard conjecture B(W x_C W)
  BOUND   bounded Hilbert data at infinitely many points, e.g. CM points
  MODP    bounded Hilbert data of l-adic representatives on a Zariski dense
          set of closed points of the arithmetic model
  EXT119  one perfect complex at one point with ch = N omega and
          dim Ext^2 = 119
  KS_U    the Kuga-Satake class of S_lambda(t) algebraic for uncountably
          many t
  HK_U    a symplectic rational map from X_t x X_t as in the proposition on
          the square as a holomorphic symplectic variety, for uncountably
          many t
  CM      the Hodge conjecture for X_c x X_c at every CM point   (proved)
  V       the variational Hodge conjecture for algebraic classes
  L       the Lefschetz standard conjecture for every variety
  M       every Hodge class is motivated
  F1, F2, F3   the three statements of the corollary on what remains
  HC      the Hodge conjecture

What is checked:

  (A) every theorem label in the rule set is a label of the paper, against
      paper_labels.txt;
  (B) TARGET is not in the closure of the proved statements;
  (C) the statements equivalent to TARGET over the proved statements are
      exactly TARGET, UNCOUNT, B_WW, BOUND and MODP;
  (D) every minimal set of open statements that yields TARGET has one
      element: one route suffices, and the five open routes of the bypass
      audit are not five obligations;
  (E) TARGET does not yield EXT119, KS_U or HK_U: those two routes are
      stronger than the target, not forms of it;
  (F) L and V each yield TARGET, so on the routes to the conjecture through
      them the target is not an input;
  (G) HC and F2 yield TARGET, and TARGET yields neither, nor any of F1, F3,
      L, V, M;
  (H) F3 is equivalent to HC (prop:f3ishc: the conjecture for the varieties
      that are not abelian covers A x P^1 and so gives the conjecture for A),
      so F3 is one more one-element route to TARGET, twelve in all, and
      TARGET is an input to no minimal route to HC.

Run:  python3 mumford_routes.py
"""
import itertools
import os

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


STATUS = {
    "TARGET": "open", "UNCOUNT": "open", "B_WW": "open", "BOUND": "open",
    "MODP": "open", "EXT119": "open", "KS_U": "open", "HK_U": "open",
    "CM": "proved", "V": "open", "L": "open", "M": "open",
    "F1": "open", "F2": "open", "F3": "open", "HC": "open",
}

# (premises, conclusion, label of the theorem that proves the implication)
RULES = [
    (("B_WW",), "TARGET", "cor:mumfordequiv"),
    (("TARGET",), "B_WW", "cor:mumfordequiv"),
    (("UNCOUNT",), "TARGET", "cor:mumfordequiv"),
    (("TARGET",), "UNCOUNT", "cor:mumfordequiv"),
    (("BOUND",), "TARGET", "cor:mumfordbounded"),
    (("TARGET",), "BOUND", "cor:mumfordbounded"),
    (("MODP",), "TARGET", "thm:modpdensity"),
    (("TARGET",), "MODP", "thm:modpdensity"),
    (("EXT119",), "TARGET", "thm:mumfordnumerical"),
    (("KS_U",), "UNCOUNT", "thm:mumfordks"),
    (("HK_U",), "UNCOUNT", "prop:hksquare"),
    (("V", "CM"), "TARGET", "thm:mumfordcm"),
    (("L",), "V", "prop:lefvhc"),
    (("HC",), "V", "prop:lefvhc"),
    (("HC",), "L", "prop:lefmot"),
    (("HC",), "M", "prop:lefmot"),
    (("L", "M"), "HC", "prop:lefmot"),
    (("F1", "F2", "F3"), "HC", "cor:fourremain"),
    (("F2",), "TARGET", "cor:fourremain"),
    (("HC",), "F2", "cor:fourremain"),
    (("F3",), "HC", "prop:f3ishc"),
    (("HC",), "F3", "prop:f3ishc"),
]


def closure(seed):
    have = set(seed)
    changed = True
    while changed:
        changed = False
        for prem, concl, _lab in RULES:
            if concl not in have and all(p in have for p in prem):
                have.add(concl)
                changed = True
    return have


def run():
    proved = {s for s, st in STATUS.items() if st == "proved"}

    # (A)
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "paper_labels.txt")) as f:
        known = {ln.strip() for ln in f if ln.strip()}
    labels = sorted({lab for _p, _c, lab in RULES})
    named = {s for p, c, _l in RULES for s in p + (c,)}
    missing = [lab for lab in labels if lab not in known]
    check("every theorem label in the rule set is a label of the paper, and "
          "every statement named in a rule is declared",
          not missing and named <= set(STATUS) and set(STATUS) <= named,
          "%d rules, %d labels" % (len(RULES), len(labels)))

    # (B)
    base = closure(proved)
    check("the target is not in the closure of the proved statements",
          "TARGET" not in base)

    # (C)
    opens = sorted(s for s, st in STATUS.items() if st == "open")
    fwd = closure(proved | {"TARGET"})
    equiv = sorted(s for s in opens
                   if "TARGET" in closure(proved | {s}) and s in fwd)
    check("the statements equivalent to the target over the proved ones are "
          "exactly TARGET, UNCOUNT, B_WW, BOUND and MODP",
          equiv == sorted(["TARGET", "UNCOUNT", "B_WW", "BOUND", "MODP"]),
          "%s" % equiv)

    # (D)
    cands = [s for s in opens if s != "TARGET"]
    minimal = []
    for k in range(1, len(cands) + 1):
        for S in itertools.combinations(cands, k):
            if any(set(m) <= set(S) for m in minimal):
                continue
            if "TARGET" in closure(proved | set(S)):
                minimal.append(S)
    sizes = sorted({len(m) for m in minimal})
    check("every minimal set of open statements yielding the target has one "
          "element, so one route suffices",
          sizes == [1] and len(minimal) == 12,
          "%d minimal sets: %s" % (len(minimal),
                                   ", ".join(m[0] for m in minimal)))

    # (E)
    stronger = ["EXT119", "KS_U", "HK_U"]
    check("the target yields none of EXT119, KS_U, HK_U: those routes are "
          "stronger than the target, not forms of it",
          all(s not in fwd for s in stronger)
          and all("TARGET" in closure(proved | {s}) for s in stronger))

    # (F)
    check("L and V each yield the target, so on the routes to the conjecture "
          "through them the target is not an input",
          "TARGET" in closure(proved | {"L"})
          and "TARGET" in closure(proved | {"V"}))

    # (G)
    check("HC and F2 yield the target, and the target yields none of HC, F1, "
          "F2, F3, L, V, M",
          "TARGET" in closure({"HC"}) and "TARGET" in closure({"F2"})
          and all(s not in fwd for s in ["HC", "F1", "F2", "F3", "L", "V",
                                          "M"]))

    # (H)
    f3 = closure(proved | {"F3"})
    hc = closure(proved | {"HC"})
    check("F3 is equivalent to HC and is itself a one-element route to the "
          "target",
          "HC" in f3 and "F3" in hc and "TARGET" in f3
          and ("F3",) in minimal,
          "by prop:f3ishc; so the three statements of cor:fourremain are not "
          "three obligations either")
    need = []
    for k in range(1, len(cands) + 1):
        for S in itertools.combinations(cands, k):
            if any(set(m) <= set(S) for m in need):
                continue
            if "HC" in closure(proved | set(S)):
                need.append(S)
    check("the minimal sets of open statements yielding HC in this rule set "
          "are {HC}, {F3} and {L, M}, and none contains the target",
          sorted(need) == sorted([("HC",), ("F3",), ("L", "M")])
          and all("TARGET" not in m for m in need),
          "%s" % ", ".join("{" + ", ".join(m) + "}" for m in need))


if __name__ == "__main__":
    print("(XLIX) which of the open routes to the Mumford target are needed")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
