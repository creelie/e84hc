#!/usr/bin/env python3
"""
closure_f3prime_mot.py  (attack13/A4)

Adds to the rule set of code/closure_graph.py (read-only import, the repository
is not modified) the implication proved in Theorem C of the A4 report:

    (F3')  ==>  (M)

(red_ab_mod ==> mot), which holds because
  * every Hodge class on an abelian variety is motivated (Andre 1996,
    Theoreme 0.6.2), quoted as "mot_ab";
  * motivated classes contain the algebraic classes and are stable under
    pull-back, cup product and push-forward (Andre 1996, section 2), so under
    every algebraic correspondence, quoted as "mot_corr".

It then recomputes, exhaustively, the minimal sufficient sets, and checks
  (1) the five minimal sets are unchanged;
  (2) the closure of {lef_B, red_ab_mod} now contains mot, i.e. the route
      {L, F3'} passes through the route {L, M};
  (3) every minimal sufficient set now implies mot inside the rule set,
      except {red_ab} (which implies HC, hence mot only through HC, and
      HC => mot is recorded outside the Horn rules);
  (4) mot alone is still insufficient, and red_ab_mod alone is still
      insufficient.
"""
import importlib.util
import os
import sys
from itertools import combinations

PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "closure_graph.py")
spec = importlib.util.spec_from_file_location("cg", PATH)
cg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cg)

STATEMENTS = dict(cg.STATEMENTS)
RULES = list(cg.RULES)

STATEMENTS["mot_ab"] = ("quoted", "every Hodge class on an abelian variety is "
                        "motivated (Andre 1996, Th. 0.6.2)")
STATEMENTS["mot_corr"] = ("quoted", "motivated classes are stable under "
                          "algebraic correspondences (Andre 1996, sec. 2)")
RULES.append((("red_ab_mod", "mot_ab", "mot_corr"), "mot", "A4:thmC"))

BASE = {s for s, v in STATEMENTS.items() if v[0] in ("proved", "quoted")}
LEAVES = sorted(s for s, v in STATEMENTS.items() if v[0] == "open")


def closure(seed, rules):
    have = set(seed)
    changed = True
    while changed:
        changed = False
        for prem, conc, _ in rules:
            if conc not in have and all(p in have for p in prem):
                have.add(conc)
                changed = True
    return have


def minimal_sets(rules):
    suff = []
    for k in range(len(LEAVES) + 1):
        for S in combinations(LEAVES, k):
            if any(set(T) <= set(S) for T in suff):
                continue
            if "HC" in closure(BASE | set(S), rules):
                suff.append(S)
    return sorted(suff)


npass = nfail = 0


def check(name, ok, detail=""):
    global npass, nfail
    if ok:
        npass += 1
    else:
        nfail += 1
    print(("[PASS] " if ok else "[FAIL] ") + name + ("  " + detail if detail else ""))


old = minimal_sets(cg.RULES)
new = minimal_sets(RULES)
print("open statements:", len(LEAVES), " subsets:", 2 ** len(LEAVES))
print("minimal sets, old rule set:", old)
print("minimal sets, with F3' => M:", new)
check("minimal sufficient sets unchanged by the rule F3' => M", old == new)
c = closure(BASE | {"lef_B", "red_ab_mod"}, RULES)
check("closure of {lef_B, red_ab_mod} contains mot", "mot" in c)
check("closure of {red_ab_mod} contains mot but not HC",
      "mot" in closure(BASE | {"red_ab_mod"}, RULES)
      and "HC" not in closure(BASE | {"red_ab_mod"}, RULES))
check("closure of {mot} does not contain HC",
      "HC" not in closure(BASE | {"mot"}, RULES))
for S in new:
    cl = closure(BASE | set(S), RULES)
    print("   ", S, "-> mot in closure:", "mot" in cl)
check("every minimal set other than {red_ab} derives mot inside the rules",
      all("mot" in closure(BASE | set(S), RULES) for S in new if S != ("red_ab",)))
# the route {lef_B, red_ab_mod} is dominated by {lef_B, mot}: its closure
# contains the other set
check("{lef_B, red_ab_mod} derives every member of {lef_B, mot}",
      {"lef_B", "mot"} <= closure(BASE | {"lef_B", "red_ab_mod"}, RULES))
print("%d checks passed, %d failed" % (npass, nfail))
sys.exit(1 if nfail else 0)
