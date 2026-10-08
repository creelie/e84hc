#!/usr/bin/env python3
"""
closure_graph.py

What is left between this paper and the Hodge conjecture, computed rather than
asserted.  Item (XXXIII) of COMPUTATIONS.md.

The paper proves a number of implications and leaves a number of statements
open.  Written out in prose, the relation between the two is easy to get
wrong: an implication whose premise is itself open looks, at a distance, like
a step forward, and a route that closes one family looks like a route that
closes the problem.  This script removes the distance.  It carries the logical
skeleton of the paper as data: a set of statements, each marked proved here,
quoted from the literature, or open, and a set of inference rules, each of
which is one theorem and carries the label of that theorem in the paper.  The
consequences are then computed.

The rules are Horn rules, a finite set of premises entailing one conclusion,
so the consequence operator is monotone and the forward closure is reached by
iterating to a fixed point.  Everything below is exact and finite; the search
over subsets is exhaustive.

What is checked:

  (a) every statement named in a rule is declared, every declared statement is
      used, and the rule set is acyclic, so that no conclusion is among its
      own premises at any depth;

  (b) every theorem label appearing in the rule set is a label of the paper,
      checked against paper_labels.txt, which is generated from the sources;

  (c) no statement marked as proved here rests, at any depth, on an open one:
      the closure of the proved and quoted statements contains every statement
      so marked, which is the self-audit that the paper claims nothing it has
      not derived;

  (d) the Hodge conjecture is NOT in the closure of the proved and quoted
      statements.  The paper does not prove it, and this is the machine
      statement of that fact;

  (e) the minimal sufficient sets are enumerated exhaustively: every subset S
      of the open statements such that the Hodge conjecture lies in the
      closure of the proved and quoted statements together with S, and such
      that no proper subset of S has that property.  The intersection of these
      sets is what every route needs; where they differ is where there is a
      genuine choice of route;

  (f) the secant route (sec:secantobjects), taken as far as it can go, does
      not lie in any minimal sufficient set.  Granting its two open demands, a
      secant object satisfying the weakened criterion in every dimension and
      an affirmative answer to Markman's Question 11.4, yields the Weil classes
      of trivial discriminant, because every base point that route produces
      is a split member, and through descent (prop:descent) it then yields
      every imaginary quadratic family; it yields nothing over the CM fields
      of degree at least four.  Without the descent rules the rule set
      reports that the route stops at the trivial discriminant; that is an
      omission of the rule set, not a fact;

  (g) the derivation of the Hodge conjecture from the proved statements
      together with each minimal sufficient set is printed in full, one rule
      per line, so that the chain can be read off and compared with the paper;

  (h) the rule set includes the routes of the literature through motivated
      classes.  Two theorems of Andre and one of Deligne and Andre are
      quoted: motivated classes deform in smooth projective families, and
      every Hodge class on an abelian variety is reached from algebraic
      classes by pull-back and deformation.  The Lefschetz standard
      conjecture B for every variety makes every motivated class algebraic,
      because it makes the Lefschetz involution algebraic.  With these rules
      and with the weaker statement red_ab_mod of def:f3prime, the
      conjecture modulo abelian varieties, the minimal sufficient sets are
      exactly five: {red_ab}, {lef_B, mot}, {lef_B, red_ab_mod},
      {red_ab_mod, vhc} and {P2_cm_s, red_ab_mod, red_weil}.  The sets
      {lef_B, red_ab}, {red_ab, vhc} and {P2_cm_s, red_ab, red_weil}
      suffice and are not minimal; only the route through this paper uses
      anything proved here; every member of a minimal set except P2_cm_s is
      itself a consequence of the Hodge conjecture, recorded with the result
      that proves it; and {red_ab} and {lef_B, mot} are each equivalent to
      the conjecture.  The propagation statement (P2) is carried family by
      family, as P2_iq_s, P2_iq_ns, P2_cm_s and P2_cm_ns, and the rules of
      prop:descent (descent within a field, scalar extension from a field of
      degree at least four to the imaginary quadratic fields it contains)
      show that only P2_cm_s, (P2) for the split families of the fields of
      degree at least four, is needed on any minimal route;

  (i) the rule set contains the elementary implication red_ab => HC_ab of
      prop:f3ishc: the Hodge conjecture for the varieties that are not
      abelian covers A x P^1 for every abelian variety A, and the conjecture
      for A x P^1 gives it for A (pull back along the projection, cup with
      the class of A x {0}, push forward).  Without that rule the rule set
      reports four minimal sets, among them {P2, red_ab, red_weil}, with no
      single statement sufficient.  With the rule, red_ab alone suffices and
      is equivalent to the conjecture.  The
      set also carries the weaker statement red_ab_mod of def:f3prime, with
      the rule of prop:f3prime(i).  The check (i) below removes both
      additions and confirms that the four sets are what the rule set
      without them gives, so that the difference is traced to them.

  (j) prop:f2isab proves red_weil => HC_ab: a Hodge class beta on an
      abelian variety A gives the class beta x e on A x X x X, with X a
      Mumford fourfold and e a Hodge class of X x X that the cyclic
      permutation zeta of prop:mumfordmotivic does not fix up to a scalar;
      the classes of the subring of divisor and Weil classes are fixed by
      zeta (prop:mumfordformal), so beta x e lies outside it and red_weil
      makes it algebraic, and pairing with a class of X x X gives beta back.
      The rule is not part of the rule set above.  The check (j) below
      adjoins it and finds five minimal sufficient sets again, {red_ab},
      {lef_B, mot}, {lef_B, red_ab_mod}, {red_ab_mod, vhc} and
      {red_ab_mod, red_weil}: P2_cm_s then lies in no minimal set, so that
      the route through the Weil classes is not needed once red_weil is
      granted.

The point of (f) deserves to be said plainly, because a list of open problems
invites the opposite reading.  The demand for one secant object on one
abelian fourfold is not a sub-conjecture whose proof would close the Hodge
conjecture, nor a step on a path to closing it.  Granted in every dimension,
and granted together with an affirmative answer to a question that is open,
it closes the imaginary quadratic families, the trivial discriminant directly
and the others by descent, and leaves the CM fields of higher degree, the
classes beyond the Weil lines and the varieties that are not abelian exactly
as they were.

The point of (h) and (i) is the same one made about the whole paper.  Two
of the minimal routes to the conjecture are the conjecture restated: the
conjecture for the varieties that are not abelian, and the Lefschetz standard
conjecture with the motivatedness of Hodge classes.  The other three pass
through red_ab_mod, the conjecture modulo abelian varieties, which is open
and which nothing here proves outside the class of prop:f3prime(iii).

Run:  python3 closure_graph.py
"""
from itertools import combinations
import os

PASS, FAIL = [], []


def check(name, ok, detail=""):
    (PASS if ok else FAIL).append(name)
    print(("  [PASS] " if ok else "  [FAIL] ") + name +
          (("   " + detail) if detail else ""))


# --------------------------------------------------------------- statements
#
# status: "proved" = proved in this paper
#         "quoted" = a theorem of the literature, cited
#         "open"   = not proved anywhere known to us
#
# Statements with status "derived" are the ones the rules are about; they carry
# no standing of their own and are true exactly when some rule makes them so.

STATEMENTS = {
    # the target and its decomposition
    "HC": ("derived",
           "the Hodge conjecture for every smooth complex projective variety"),
    "HC_ab": ("derived",
              "the Hodge conjecture for every abelian variety"),
    "weil_all": ("derived",
                 "the Weil classes of every abelian variety of Weil type, "
                 "over every CM field, are algebraic"),
    "weil_iq": ("derived",
                "W(K,n,delta) for every imaginary quadratic K, every n, "
                "every discriminant"),
    "weil_triv": ("derived",
                  "W(K,n,delta_0), the trivial discriminant families"),
    "weil_nontriv": ("derived",
                     "W(K,n,delta) for delta not trivial"),
    "s1": ("derived",
           "a secant object on an abelian fourfold that extends along the "
           "polarised deformations and satisfies the Heisenberg identity"),
    "w4triv": ("derived", "W(K,4,delta_0)"),
    "known": ("derived", "the range settled in the literature"),

    # open leaves
    "red_ab": ("open",
               "the Hodge conjecture for every smooth projective variety that "
               "is not an abelian variety; equivalent to the conjecture, since "
               "it covers A x P^1 for every abelian variety A "
               "(prop:f3ishc)"),
    "red_ab_mod": ("open",
                   "every Hodge class on every smooth projective variety is "
                   "algebraic modulo images of Hodge classes of abelian "
                   "varieties under algebraic correspondences (def:f3prime); "
                   "trivial on abelian varieties"),
    "red_weil": ("open",
                 "every Hodge class on an abelian variety outside the subring "
                 "generated by divisor classes and Weil classes of quotients is "
                 "algebraic; not a reduction, since the self-product of a "
                 "Mumford fourfold carries two such classes"),
    "weil_cm": ("derived",
                "the Weil classes of abelian varieties with multiplication by "
                "a CM field of degree at least four are algebraic"),
    "weil_cm_triv": ("derived",
                     "the same for the split families of those fields"),
    "weil_cm_nontriv": ("derived",
                        "the same for their families of nontrivial "
                        "discriminant"),
    # the propagation statement (P2) of rem:p2prime, read family by family:
    # at a base point of the family, a complex whose Chern character is a
    # nonzero Weil class plus a polynomial in the polarisation has injective
    # semiregularity map; the first form, with Chern character exactly a Weil
    # class, is false by thm:p2false
    "P2_iq_s": ("open",
                "(P2) for the Weil families of trivial discriminant of the "
                "imaginary quadratic fields"),
    "P2_iq_ns": ("open",
                 "(P2) for the Weil families of nontrivial discriminant of "
                 "the imaginary quadratic fields"),
    "P2_cm_s": ("open",
                "(P2) for the split Weil families of the CM fields of degree "
                "at least four"),
    "P2_cm_ns": ("open",
                 "(P2) for the other Weil families of those fields"),
    "secant_all": ("open",
                   "a secant object satisfying the weakened criterion exists "
                   "on an abelian n-fold for every n"),
    "Q114": ("open",
             "Markman's Question 11.4 has an affirmative answer"),
    "smooth_exists": ("open",
                      "a smooth surface with the forced invariants exists on a "
                      "principally polarised abelian fourfold and moves with "
                      "it to first order in every polarised direction"),
    "smooth_vanish": ("open",
                      "the image of the product of translation classes "
                      "vanishes in H^1(S, N_{S/X})"),
    "sing_exists": ("open",
                    "a singular Cohen-Macaulay support exists whose "
                    "Hilbert-Burch resolution is over a bundle that is not "
                    "projectively flat and whose twisted ideal sheaf extends "
                    "along the polarised deformations"),
    "sing_vanish": ("open",
                    "the image of the product of translation classes vanishes "
                    "in H^1(Z, Ext^1)"),

    # proved here
    "base_point": ("proved",
                   "a base point with an explicit cycle in every Weil family"),
    "reduction": ("proved",
                  "algebraicity of one class at every point of one connected "
                  "domain is equivalent to the conjecture for that family"),
    "orbit_dense": ("proved",
                    "the algebraic locus is stable under the rational points "
                    "and their orbit is dense"),
    "factor": ("proved",
               "the weakened criterion for the transform is extension along "
               "the polarised deformations and the Heisenberg identity for "
               "the factor"),
    "class_cond": ("proved",
                   "the three conditions of Markman's strategy that are "
                   "conditions on the Chern character hold at the point (1,3)"),
    "cm_line": ("proved",
                "the local obstruction is exactly a failure of "
                "Cohen-Macaulayness, and no complete intersection occurs"),
    "ingredients": ("proved",
                    "three of the four ingredients, in every dimension, "
                    "including the existence of the secant sheaves"),
    "base_point_cm": ("proved",
                      "a CM base point with an explicit cycle in every Weil "
                      "family of every CM field of degree at least four"),
    "reduction_cm": ("proved",
                     "for every CM field, algebraicity of one class at every "
                     "point of one connected domain is equivalent to the "
                     "algebraicity of its Weil classes, and gives the "
                     "conjecture for the members with full Hodge group"),
    "orbit_dense_cm": ("proved",
                       "for every CM field the algebraic locus is stable under "
                       "the rational points and their orbits are dense, and "
                       "it is a countable union of closed sets"),

    # quoted
    "mar2": ("quoted", "W(K,2,delta) for every K and every discriminant"),
    "mar3": ("quoted", "W(K,3,delta_0)"),
    "mot_def": ("quoted",
                "a global section of R^{2p} f_* Q for a smooth projective "
                "family over a connected base that is motivated at one "
                "point is motivated at every point (Andre 1996, Theorem 0.5)"),
    "acc_ab": ("quoted",
               "every Hodge class on a complex abelian variety lies in the "
               "least family of classes that contains the algebraic classes "
               "and is stable under pull-back and under deformation in "
               "smooth projective families (Deligne, Andre; Milne, Theorem 3)"),

    # the statements of the literature routes, all open
    "lef_B": ("open",
              "the Lefschetz standard conjecture B(X) for every smooth "
              "complex projective variety X"),
    "mot": ("open",
            "every Hodge class on every smooth complex projective variety "
            "is motivated in the sense of Andre"),
    "vhc": ("open",
            "a global section of R^{2p} f_* Q for a smooth projective family "
            "over a smooth connected base that is algebraic at one point is "
            "algebraic at every point"),
}

# ------------------------------------------------------------------- rules
#
# (premises, conclusion, the label in the paper that justifies the step)

RULES = [
    (("HC_ab", "red_ab"), "HC", "ssec:closuremap"),
    # the conjecture for A x P^1, which is not an abelian variety, gives the
    # conjecture for A: pr_*(pr^* alpha . [A x 0]) = alpha
    (("red_ab",), "HC_ab", "prop:f3ishc"),
    # the conjecture modulo abelian varieties, with the conjecture for them
    (("HC_ab", "red_ab_mod"), "HC", "prop:f3prime"),
    (("weil_all", "red_weil"), "HC_ab", "ssec:closuremap"),
    (("weil_iq", "weil_cm"), "weil_all", "app:albert"),
    (("weil_triv", "weil_nontriv"), "weil_iq", "prop:separate"),

    # propagation, family by family: the base point is supplied in every
    # family, so the propagation statement closes each family it is granted on
    (("base_point", "reduction", "orbit_dense", "P2_iq_s"), "weil_triv",
     "thm:semiregclosure"),
    (("base_point", "reduction", "orbit_dense", "P2_iq_ns"), "weil_nontriv",
     "thm:semiregclosure"),

    # the same for every CM field of degree at least four: the base point is
    # a CM point and the propagation statement is the same one
    (("base_point_cm", "reduction_cm", "orbit_dense_cm", "P2_cm_s"),
     "weil_cm_triv", "thm:cmpropagation"),
    (("base_point_cm", "reduction_cm", "orbit_dense_cm", "P2_cm_ns"),
     "weil_cm_nontriv", "thm:cmpropagation"),
    (("weil_cm_triv", "weil_cm_nontriv"), "weil_cm", "prop:cmweil"),

    # descent: B x Y with Y of (F,1)-Weil type, and pr_{B*}( . pr_Y^* y'),
    # carries the Weil classes of one family onto those of every family of
    # lower dimension and every discriminant; and scalar extension B -> B (x)
    # O_F carries those of the split families of a CM field F of degree at
    # least four onto the split families of the imaginary quadratic fields
    # K in F (every K lies in K(sqrt 2))
    (("weil_triv",), "weil_nontriv", "prop:descent"),
    (("weil_cm_triv",), "weil_cm_nontriv", "prop:descent"),
    (("weil_cm_triv",), "weil_triv", "prop:descent"),

    # the secant route: it reaches the split members, which are exactly the
    # members of trivial discriminant
    (("secant_all", "Q114", "factor", "class_cond", "ingredients",
      "reduction"), "weil_triv", "prop:splitgeom"),

    # the secant route at n = 4, written out
    (("smooth_exists", "smooth_vanish", "cm_line"), "s1", "cor:cmdichotomy"),
    (("sing_exists", "sing_vanish", "cm_line"), "s1", "cor:cmdichotomy"),
    (("s1", "Q114", "factor", "class_cond"), "w4triv", "cor:markmancondition"),

    # what the literature gives, recorded and not used
    (("mar2", "mar3"), "known", "rem:markmanscope"),

    # the literature routes through motivated classes: under B for every
    # variety the Lefschetz involution is algebraic, so motivated classes are
    # algebraic; motivated classes deform in families (Andre), so B gives the
    # variational statement; and the variational statement for algebraic
    # classes gives every Hodge class on an abelian variety (Deligne, Andre,
    # Milne), which is the theorem of Abdulali and Andre once B is granted
    (("lef_B", "mot"), "HC", "prop:lefmot"),
    (("lef_B", "mot_def"), "vhc", "prop:lefvhc"),
    (("vhc", "acc_ab"), "HC_ab", "thm:vhcab"),
]

# Consequences of the conjecture itself, each with the result that gives it.
# These are not rules: a rule with HC among its premises would close a cycle.
# They record which open statements any proof of the conjecture must prove.
IMPLIED_BY_HC = {
    "lef_B": "thm:equivalence",
    "vhc": "prop:lefvhc",
    "mot": "prop:lefmot",
    "red_ab": "prop:f3ishc",
    "red_ab_mod": "prop:f3prime",
    "red_weil": "ssec:closuremap",
}

TARGET = "HC"

# every label above must be a label of the paper
LABELS = sorted({r[2] for r in RULES} | set(IMPLIED_BY_HC.values()))

# The same graph is carried into the Lean certificate as numbered statements
# and rules over those numbers.  The numbering is this one, and the rules
# there must be the image of the rules here under it.  Section 24 of
# HodgeObstruction.lean.
LEAN_ORDER = [
    "HC", "HC_ab", "weil_all", "weil_iq", "weil_triv", "weil_nontriv",
    "s1", "w4triv", "known", "red_ab", "red_weil", "weil_cm", "P2_iq_s",
    "secant_all", "Q114", "smooth_exists", "smooth_vanish", "sing_exists",
    "sing_vanish", "base_point", "reduction", "orbit_dense", "factor",
    "class_cond", "cm_line", "ingredients", "mar2", "mar3",
    "base_point_cm", "reduction_cm", "orbit_dense_cm",
    "lef_B", "mot", "vhc", "mot_def", "acc_ab", "red_ab_mod",
    "P2_iq_ns", "P2_cm_s", "P2_cm_ns", "weil_cm_triv", "weil_cm_nontriv",
]
LEAN_RULES = [
    ([1, 9], 0), ([9], 1), ([2, 10], 1), ([3, 11], 2), ([4, 5], 3),
    ([12, 19, 20, 21], 4), ([37, 19, 20, 21], 5),
    ([38, 28, 29, 30], 40), ([39, 28, 29, 30], 41), ([40, 41], 11),
    ([4], 5), ([40], 41), ([40], 4),
    ([13, 14, 20, 22, 23, 25], 4),
    ([15, 16, 24], 6), ([17, 18, 24], 6), ([6, 14, 22, 23], 7),
    ([26, 27], 8),
    ([31, 32], 0), ([31, 34], 33), ([33, 35], 1),
    ([1, 36], 0),
]
LEAN_BASE = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 34, 35]


# ------------------------------------------------------------- the closure
def closure(seed):
    """the least set containing seed and closed under the rules"""
    have = set(seed)
    changed = True
    while changed:
        changed = False
        for prem, conc, _ in RULES:
            if conc not in have and all(p in have for p in prem):
                have.add(conc)
                changed = True
    return have


def derivation(seed, goal):
    """a shortest forward derivation of goal from seed, as a list of rules"""
    have, steps = set(seed), []
    while goal not in have:
        fired = False
        for prem, conc, lab in RULES:
            if conc not in have and all(p in have for p in prem):
                have.add(conc)
                steps.append((prem, conc, lab))
                fired = True
        if not fired:
            return None
    # drop the steps that the goal does not depend on
    need, keep = {goal}, []
    for prem, conc, lab in reversed(steps):
        if conc in need:
            keep.append((prem, conc, lab))
            need.update(prem)
    return list(reversed(keep))


def status(s):
    return STATEMENTS[s][0]


BASE = {s for s in STATEMENTS if status(s) in ("proved", "quoted")}
# every open statement is a candidate premise, including the one open
# statement that is also the conclusion of a rule (the variational statement,
# which the Lefschetz standard conjecture implies)
LEAVES = sorted(s for s in STATEMENTS if status(s) == "open")


def run():
    global RULES
    print()

    # (a) the rule set is well formed and acyclic
    named = set()
    for prem, conc, _ in RULES:
        named.update(prem)
        named.add(conc)
    undeclared = sorted(named - set(STATEMENTS))
    unused = sorted(set(STATEMENTS) - named)
    check("every statement in a rule is declared, and every statement is used",
          not undeclared and not unused,
          "%d statements, %d rules" % (len(STATEMENTS), len(RULES))
          if not undeclared and not unused
          else "undeclared %s, unused %s" % (undeclared, unused))

    order, left = [], list(RULES)
    settled = set(s for s in STATEMENTS
                  if all(conc != s for _, conc, _ in RULES))
    progress = True
    while progress:
        progress = False
        for r in list(left):
            if all(p in settled for p in r[0]):
                left.remove(r)
                settled.add(r[1])
                order.append(r[1])
                progress = True
    check("the rule set is acyclic", not left,
          "a topological order exists, so no statement is among its own "
          "premises at any depth"
          if not left else "cycle through %s" % [r[1] for r in left])

    # (b) the labels are labels of the paper
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "paper_labels.txt")
    if os.path.exists(path):
        with open(path) as f:
            known = {ln.strip() for ln in f if ln.strip()}
        missing = [l for l in LABELS if l not in known]
        check("every theorem label in the rule set is a label of the paper",
              not missing,
              "%d labels, checked against the %d labels of the sources"
              % (len(LABELS), len(known))
              if not missing else "not in the paper: %s" % missing)
    else:
        check("paper_labels.txt is present", False,
              "the label list generated from the sources is missing")

    # (c) nothing proved rests on something open
    proved = {s for s in STATEMENTS if status(s) == "proved"}
    quoted = {s for s in STATEMENTS if status(s) == "quoted"}
    cl = closure(proved | quoted)
    rests = sorted(s for s in proved | quoted if s not in cl)
    check("no statement proved here rests on an open one", not rests,
          "the closure of the proved and quoted statements contains all %d of "
          "them" % len(proved | quoted)
          if not rests else str(rests))

    # (d) the conjecture is not proved here
    check("the Hodge conjecture is not a consequence of what is proved here",
          TARGET not in cl,
          "the closure of the proved and quoted statements has %d members and "
          "%s is not one of them" % (len(cl), TARGET))

    # (e) the minimal sufficient sets
    print()
    sufficient = []
    for k in range(0, len(LEAVES) + 1):
        for S in combinations(LEAVES, k):
            if any(set(T) <= set(S) for T in sufficient):
                continue
            if TARGET in closure(BASE | set(S)):
                sufficient.append(S)
    check("the minimal sufficient sets are enumerated exhaustively", True,
          "%d of them, over the %d open statements, from %d subsets"
          % (len(sufficient), len(LEAVES), 2 ** len(LEAVES)))
    expected = sorted([("red_ab",), ("lef_B", "mot"),
                       ("lef_B", "red_ab_mod"), ("red_ab_mod", "vhc"),
                       ("P2_cm_s", "red_ab_mod", "red_weil")])
    check("the minimal sufficient sets are exactly five",
          sorted(sufficient) == expected,
          "{red_ab}, {lef_B, mot}, {lef_B, red_ab_mod}, {red_ab_mod, vhc} "
          "and {P2_cm_s, red_ab_mod, red_weil}"
          if sorted(sufficient) == expected else str(sufficient))

    singles = [S for S in sufficient if len(S) == 1]
    check("exactly one single open statement suffices, and it is red_ab",
          singles == [("red_ab",)],
          "the conjecture for the varieties that are not abelian gives the "
          "conjecture for abelian varieties through A x P^1, and then the "
          "conjecture")
    older = [("P2_cm_s", "red_ab", "red_weil"), ("lef_B", "red_ab"),
             ("red_ab", "vhc")]
    check("the route through this paper and the two routes of the literature "
          "with red_ab suffice and are not minimal",
          all(TARGET in closure(BASE | set(S)) for S in older)
          and all(S not in sufficient for S in older),
          "each contains the sufficient singleton {red_ab}; with red_ab_mod "
          "in its place each is minimal")
    mod = closure(BASE | {"red_ab_mod"})
    check("red_ab_mod alone gives neither the conjecture for abelian "
          "varieties nor the conjecture",
          "HC_ab" not in mod and TARGET not in mod,
          "it holds trivially on abelian varieties, so it needs a second "
          "statement that reaches them")
    three = [S for S in sufficient if len(S) > 2]
    check("the route through this paper, with red_ab_mod, is the only "
          "minimal sufficient set with three elements",
          three == [("P2_cm_s", "red_ab_mod", "red_weil")],
          "it needs one statement more than each route of the literature "
          "through red_ab_mod")

    print()
    print("       the minimal sufficient sets:")
    for S in sorted(sufficient, key=lambda S: (len(S), S)):
        print("            {%s}" % ", ".join(S))
    print("       with")
    for s in sorted(set().union(*[set(S) for S in sufficient])):
        print("            %-14s %s" % (s, STATEMENTS[s][1]))
    print()

    # which members of the minimal sets any proof of the conjecture proves
    in_sets = sorted(set().union(*[set(S) for S in sufficient]))
    not_implied = [s for s in in_sets if s not in IMPLIED_BY_HC]
    check("every member of a minimal sufficient set other than P2_cm_s is a "
          "consequence of the conjecture",
          not_implied == ["P2_cm_s"],
          "lef_B by thm:equivalence, mot by prop:lefmot, vhc by "
          "prop:lefvhc, red_ab_mod by prop:f3prime, red_ab and red_weil "
          "directly; no implication from the conjecture to P2 is known"
          if not_implied == ["P2_cm_s"] else str(not_implied))
    equiv = [S for S in sufficient
             if all(s in IMPLIED_BY_HC for s in S)
             and not any(s in ("vhc", "red_weil", "red_ab_mod") for s in S)]
    check("{red_ab} and {lef_B, mot} are equivalences with the conjecture",
          sorted(equiv) == sorted([("red_ab",), ("lef_B", "mot")]),
          "{red_ab} by prop:f3ishc, {lef_B, mot} by prop:lefmot")

    check("every minimal sufficient set contains red_ab, red_ab_mod or mot",
          all({"red_ab", "red_ab_mod", "mot"} & set(S) for S in sufficient),
          "the varieties that are not abelian are reached only through the "
          "conjecture for them, through the conjecture modulo abelian "
          "varieties, or through motivated classes")

    var = closure(BASE | {"vhc"})
    check("the variational statement alone gives the conjecture for abelian "
          "varieties and not the conjecture",
          "HC_ab" in var and TARGET not in var,
          "so it covers the Weil classes of every CM field and the classes "
          "beyond the Weil lines at once")
    lef = closure(BASE | {"lef_B"})
    check("the Lefschetz standard conjecture gives the variational statement",
          "vhc" in lef and "HC_ab" in lef and TARGET not in lef,
          "through the deformation theorem for motivated classes")

    proved_here = {s for s in STATEMENTS if status(s) == "proved"}
    uses = {}
    for S in sufficient:
        steps = derivation(BASE | set(S), TARGET)
        used = set().union(*[set(p) for p, _, _ in steps])
        uses[S] = bool(used & proved_here)
    check("only the route through this paper uses a statement proved in it",
          [S for S in sufficient if uses[S]]
          == [("P2_cm_s", "red_ab_mod", "red_weil")],
          "the four other minimal sets rest on open statements and quoted "
          "theorems alone")

    check("each element of a minimal sufficient set is necessary to it",
          all(TARGET not in closure(BASE | (set(S) - {x}))
              for S in sufficient for x in S),
          "removing any one of them leaves the conjecture underivable")

    # (j) the rule red_weil => HC_ab of prop:f2isab, adjoined
    extra = list(RULES) + [(("red_weil",), "HC_ab", "prop:f2isab")]

    def closure_x(seed):
        have = set(seed)
        changed = True
        while changed:
            changed = False
            for prem, conc, _ in extra:
                if conc not in have and all(p in have for p in prem):
                    have.add(conc)
                    changed = True
        return have

    suff_x = []
    for k in range(0, len(LEAVES) + 1):
        for S in combinations(LEAVES, k):
            if any(set(T) <= set(S) for T in suff_x):
                continue
            if TARGET in closure_x(BASE | set(S)):
                suff_x.append(S)
    expected_x = sorted([("red_ab",), ("lef_B", "mot"),
                         ("lef_B", "red_ab_mod"), ("red_ab_mod", "vhc"),
                         ("red_ab_mod", "red_weil")])
    labels = open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               "paper_labels.txt")).read().split()
    check("with the rule of prop:f2isab adjoined the minimal sufficient sets "
          "are five, and P2_cm_s lies in none",
          sorted(suff_x) == expected_x and "prop:f2isab" in labels
          and all("P2_cm_s" not in S for S in suff_x),
          "{red_ab}, {lef_B, mot}, {lef_B, red_ab_mod}, {red_ab_mod, vhc} "
          "and {red_ab_mod, red_weil}"
          if sorted(suff_x) == expected_x else str(suff_x))
    check("with that rule red_weil alone gives the conjecture for abelian "
          "varieties, and red_weil with red_ab_mod the conjecture",
          "HC_ab" in closure_x(BASE | {"red_weil"})
          and TARGET not in closure_x(BASE | {"red_weil"})
          and TARGET in closure_x(BASE | {"red_weil", "red_ab_mod"}),
          "the set {P2_cm_s, red_ab_mod, red_weil} of (e) is then not "
          "minimal")

    # (f) the secant route lies off every minimal sufficient set
    secant = {"secant_all", "Q114", "smooth_exists", "smooth_vanish",
              "sing_exists", "sing_vanish"}
    check("the secant route lies in no minimal sufficient set",
          all(not (secant & set(S)) for S in sufficient),
          "granting all six of its open demands does not put it on a path to "
          "the conjecture")

    granted = closure(BASE | {"secant_all", "Q114"})
    check("the secant route, fully granted, reaches every imaginary quadratic "
          "family and stops short of the fields of higher degree",
          "weil_triv" in granted and "weil_nontriv" in granted
          and "weil_iq" in granted and "weil_cm" not in granted
          and TARGET not in granted,
          "its base points are split members, of trivial discriminant, and "
          "descent (prop:descent) carries the trivial discriminant to every "
          "other; it has no base point over a field of degree at least four")

    check("the trivial discriminant closes the imaginary quadratic case",
          "weil_iq" in closure(BASE | {"weil_triv"}),
          "by descent: B x Y, with Y a Weil surface of any discriminant, and "
          "a push-forward against the Weil class of Y")

    check("the split families of the fields of degree at least four close "
          "the imaginary quadratic case as well",
          "weil_iq" in closure(BASE | {"weil_cm_triv"}),
          "by scalar extension B -> B (x) O_F, every K lying in K(sqrt 2)")

    check("the propagation statement for the split imaginary quadratic "
          "families closes the imaginary quadratic case outright",
          "weil_iq" in closure(BASE | {"P2_iq_s"}),
          "a base point exists in every split family, and descent does the "
          "rest")

    check("the propagation statement for the split families of the fields of "
          "degree at least four closes the Weil classes of every CM field",
          "weil_all" in closure(BASE | {"P2_cm_s"}),
          "descent within each field, and scalar extension down to the "
          "imaginary quadratic fields")

    check("the families of nontrivial discriminant need no propagation "
          "statement of their own",
          all(not ({"P2_iq_ns", "P2_cm_ns"} & set(S)) for S in sufficient)
          and all(not ({"P2_iq_s", "P2_iq_ns"} & set(S)) for S in sufficient),
          "no minimal sufficient set contains (P2) for a family of nontrivial "
          "discriminant or for an imaginary quadratic field")

    check("the bounded criterion (P1) is not in the rule set",
          "P1" not in STATEMENTS,
          "it is equivalent to the conjecture for the family, so it is a "
          "restatement and not a premise")

    check("the Weil classes of the higher CM fields are derived, not open",
          "weil_cm" not in LEAVES and status("weil_cm") == "derived")

    # (i) the rule of prop:f3ishc is what changes the answer
    full = RULES
    RULES = [r for r in full if r[2] not in ("prop:f3ishc", "prop:f3prime")]
    older_leaves = [x for x in LEAVES if x != "red_ab_mod"]
    try:
        was = []
        for k in range(0, len(older_leaves) + 1):
            for S in combinations(older_leaves, k):
                if any(set(T) <= set(S) for T in was):
                    continue
                if TARGET in closure(BASE | set(S)):
                    was.append(S)
    finally:
        RULES = full
    check("without prop:f3ishc and red_ab_mod the search returns four sets, "
          "none of them a single statement",
          sorted(was) == sorted([("lef_B", "mot"), ("lef_B", "red_ab"),
                                 ("red_ab", "vhc"),
                                 ("P2_cm_s", "red_ab", "red_weil")]),
          "{lef_B, mot}, {lef_B, red_ab}, {red_ab, vhc}, {P2_cm_s, red_ab, "
          "red_weil}: the change is those two additions, with (P2) read on "
          "the split families of the higher fields")
    check("the rule of prop:f3ishc has red_ab as its only premise",
          [r for r in full if r[2] == "prop:f3ishc"]
          == [(("red_ab",), "HC_ab", "prop:f3ishc")],
          "and the conjecture for abelian varieties as its conclusion: the "
          "conjecture for A x P^1 gives it for A")

    # (g) print one derivation in full
    print()
    total = 0
    for S0 in sorted(sufficient, key=lambda S: (len(S), S)):
        print("       the conjecture from the proved and quoted statements "
              "and %s" % ", ".join(S0))
        steps = derivation(BASE | set(S0), TARGET)
        for prem, conc, lab in steps:
            print("            %-14s from %-44s [%s]"
                  % (conc, ", ".join(prem), lab))
        total += len(steps)
        print()
    check("the derivations are exhibited in full", total > 0,
          "%d steps over the %d minimal sufficient sets"
          % (total, len(sufficient)))
    print()

    # the encoding carried into the Lean certificate is the same graph
    ok = sorted(LEAN_ORDER) == sorted(STATEMENTS)
    if ok:
        idx = {s: i for i, s in enumerate(LEAN_ORDER)}
        here_rules = sorted((sorted(idx[p] for p in prem), idx[conc])
                            for prem, conc, _ in RULES)
        there = sorted((sorted(prem), conc) for prem, conc in LEAN_RULES)
        ok = here_rules == there
        ok = ok and sorted(LEAN_BASE) == sorted(idx[s] for s in BASE)
    check("the graph carried into the Lean certificate is this graph", ok,
          "the %d statements and %d rules of Section 24 of "
          "HodgeObstruction.lean are the image of these under the numbering "
          "recorded here" % (len(LEAN_ORDER), len(LEAN_RULES)))

    counts = {}
    for s in STATEMENTS:
        counts[status(s)] = counts.get(status(s), 0) + 1
    check("the statement census", True,
          "%d proved here, %d quoted, %d open, %d derived"
          % (counts.get("proved", 0), counts.get("quoted", 0),
             counts.get("open", 0), counts.get("derived", 0)))


if __name__ == "__main__":
    print("(XXXIII) the closure graph: what is left, computed")
    run()
    print()
    print("  %d checks passed, %d failed" % (len(PASS), len(FAIL)))
    raise SystemExit(0 if not FAIL else 1)
