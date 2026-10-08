# Working note: Fourier–Mukai exclusion of exponential characters at quartic CM fields

`rank88_note.tex` and `rank88_note.pdf` (9 pages, 29 September 2026) attack the
characters of rank 88 that the corrected criterion of the paper leaves open at
a quartic CM field (Theorem 19.21(v), Proposition 19.24 and Corollary 19.26 of
the paper).

- **Proved.** Tensoring by line bundles and the Fourier–Mukai conjugates of
  tensoring by line bundles on the dual act on cohomology through two commuting
  copies of sl_2, one at each real place of F_0, and preserve both dim Ext^2 and
  the rank r. The exponential shape N ω + c + Tr(a(e^{λΘ} − 1)), and its rank-104
  variant with the mixed exponential added, is carried to a Weil tori character
  and excluded whenever λ^{-1} lies in the lattice 𝔞 of the member (Theorem 4.3).
  For the linear shape N ω + c + η_s there are five constraints (Section 5).
- **Open.** The exponential shape with λ^{-1} ∉ 𝔞, the linear shape, and so
  P2_split, (F2) and (F3').
- **Earlier notes.** Section 7 checks and folds in the smooth-support note and
  the status note written in other sessions. The smooth-support statements are
  now in the paper (Lemmas 18.43, 18.56, Remark 18.44, Proposition 18.46,
  Theorem 18.57, Corollary 18.58), and Section 7.1 cites them there.

## Programs

Both use exact rational arithmetic and need Python 3 with `sympy`.

| program | what it checks | output |
|---|---|---|
| `mukai_place.py` | items (A) to (L) of Section 8: the sl_2-triples, the Weil classes, the cusp formula, the transform of Theorem 4.3, the invariance of r, the ranks 88 and 104, the linear shape | `30 checks passed, 0 failed` |
| `smooth_support.py` | the numerical statements of Section 7.1 | `25 checks passed, 0 failed` |

`mukai_place.py` imports the model of `code/quartic_rank.py` (item (LXV) of the
paper) from `../../code`. Run from this directory:

```
python3 mukai_place.py
python3 smooth_support.py
latexmk -pdf rank88_note.tex
```
