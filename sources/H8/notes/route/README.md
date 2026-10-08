# Working note: Hilbert–Burch resolutions of secant supports on abelian fourfolds

`route_note.tex` and `route_note.pdf` (6 pages, 29 September 2026) are the
corrected version of the route note written the same day for the secant route
of Section 18 of the paper.

- **Proved.** The ideal of the support of a secant object on a principally
  polarised abelian fourfold has no Hilbert–Burch resolution of rank one, so
  the support is never the zero locus of a section of a rank two bundle; at
  rank two, with Chern classes polynomial in Θ, it needs d ≡ 3 (mod 4) at b = 3,
  so d = 1 and d = 5 need rank at least three (Proposition 4.1, which is also
  Proposition 18.60 of the paper and item (LXX) of its Appendix D).
- **Corrected.** The target (the Hodge conjecture for abelian fourfolds of Weil
  type is Markman's theorem; the route aims at the Weil classes on the
  eightfolds X × X̂ and needs Question 11.4 of [Mar25b]), the place of the route
  in the closure theorem, the class [S] = NΘ², condition (a) along all ten
  polarised directions (a K-action gives at most four), the numerical lemma
  (it omits the vanishing of Chern classes above the rank; its example works
  only at d = 7) and the bibliography. Section 9 lists every change.
- **Open.** Steps 5.2 to 5.4 of the program: a support of rank at least two
  (three at d = 1, 5) over a bundle that is not projectively flat, condition (a),
  and the identity (b); Question 11.4 of [Mar25b]; and P2_split, (F2) and (F3').

## Programs

| program | what it checks | output |
|---|---|---|
| `route_checks.py` | Sections 3 to 6: the targets, the numerical lemma and its corrections, the examples, products and symmetric squares of curves, semi-homogeneous ranks, K-linear directions | `19 checks passed, 0 failed` |
| `toy/fourpartite.py`, `toy/drive2.py` | the search of Section 7 over unions of coordinate abelian surfaces in E_1 × E_2 × E_3 × E_4 (simulated annealing, not a proof) | see Section 7 |
| `toy/fat_coordinate.py` | symbolic powers of the six coordinate surfaces | no admissible character for m ≤ 20 |

`route_checks.py` needs Python 3 with `sympy` and imports the Newton-identity
helpers of `code/burch_rank.py`; the toy programs need `numpy` and were written
for the first version. Run from this directory:

```
python3 route_checks.py
python3 toy/drive2.py 1 1 "3,3,3,3;4,4,4,4" 40 60000 1 1
python3 toy/fat_coordinate.py 20
latexmk -pdf route_note.tex
```
