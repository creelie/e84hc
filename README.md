# On the Hodge conjecture for Fermat varieties

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23234362.svg)](https://doi.org/10.5281/zenodo.23234362)

**Deep Bhattacharjee**
Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

This repository holds a 65-page paper in `amsart`, its LaTeX source with the figures as PNG, and the code that re-checks its finite steps in Python, Julia, C, Lean 4 (with and without Mathlib) and Macaulay2.

## Main result

**Theorem A.** Let m = 2^a·3^b·19^c with a ≤ 1. Then the Hodge conjecture holds for the Fermat variety x₀^m + … + x_{n+1}^m = 0 of every dimension n, for every product of Fermat varieties of degree m, and for every abelian variety of Fermat type of degree m.

In particular the Hodge conjecture holds for the Fermat varieties of degree 114 in every dimension. For 57 ∤ m the theorem is Aoki's. For 57 | m the only earlier argument is a 2026 preprint of Miranda, Movasati, Rufino and Villaflor: it states the case m = 57, which by Aoki's reduction gives the others, but it ends with a statement of Kang about the Fermat fourfold of degree 114 whose proof has a gap (Remark 3.21). The proof here does not use Kang's statement, so for 57 | m it is the first complete proof, and for 114, 171, 342, 513, … the theorem had not been stated before. It does not use OpenAI's unrefereed claim of the Hodge conjecture for CM abelian varieties either, which would give every Fermat variety (Theorem E).

How it works (Section 4):

- Aoki's reduction leaves one class in degree 114: a balanced multiset β of ten residues with exactly one residue of order 19, which linear subspaces and Aoki's cycles cannot reach (Lemma 4.3, Corollary 4.5).
- β is the join of two characters α₁, α₂ of the Fermat threefold of degree 114 whose Hodge structures in H³ have level one and complementary types (Lemma 4.6).
- Each of these pieces of H³ is carried by curves. This comes from a family of curves on the threefold and a residue formula for the derivative of its Abel–Jacobi map, which extends Peterson's argument for degree 35 to a general class of "block families" (Theorem 4.16).
- One family, of cubic forms, has a residue computed by hand (Proposition 4.18). The other has degree 24, and its residue is shown to be nonzero by a certified interval computation in Arb (Proposition 4.19, Appendix B). **This is the only computer-assisted step in the paper.**
- The two pieces are joined on the product of two curves by the Lefschetz (1,1) theorem and carried to the eightfold by Shioda's inductive structure (Proposition 4.17).

## Other results

**Proved without hypothesis**

- *Theorem B.* The Hodge conjecture holds for the Fermat fourfold of every odd degree m. For m prime to 6 the proof classifies the Hodge characters: each one contains two entries a and −a, or is (x, x+m/5, x+2m/5, x+3m/5, x+4m/5, −5x) up to order (Theorem 3.9). Classes of the first kind come from linear subspaces through the inductive structure of Shioda and Ran, and those of the second kind from Aoki's cycles, pulled back along a covering of Fermat fourfolds. The only analytic input is B₁,χ ≠ 0 for odd primitive characters χ. The classification is proved in Lean 4 with Mathlib, including B₁,χ ≠ 0; only the geometric inputs remain hypotheses there. For odd m divisible by 3, Section 3.7 proves by hand that every Hodge character that generates Z/m and contains no pair a, −a can be traded, through Aoki's cycles, for algebraic classes and a character of smaller order profile, unless it is one of three exceptional characters, in degrees 21, 33 and 39 (Theorem 3.27), which identities at levels 21, 66 and 78 close (Lemma 3.26). The theorem is new for the odd m > 199 that are divisible by 3 or 5 and have a prime factor above 7 (first cases 201, 205, 207, 213, 215).
- *Theorem C.* The Hodge conjecture (HC) is equivalent to each of the following:
  - (F2) ∧ (F3′)
  - (L) ∧ (F3′)
  - (V) ∧ (F3′)
  - (CM) ∧ (IP) ∧ (F3′)
  - (L) ∧ (M)

  Here (F2) is HC for abelian varieties, (F3′) is HC modulo abelian varieties, (L) is the Lefschetz standard conjecture, (M) says every Hodge class is motivated, (V) is the variational Hodge conjecture, (CM) is HC for abelian varieties of CM type, and (IP) is propagation of algebraic classes from CM points.
- *Theorem D.* These are all the routes. Every set of the statements from which HC follows implies (F2) and (F3′). The only way to avoid assuming both is the pair (L) ∧ (M), which is equivalent to HC.
- *Theorem E* (unconditional part). (F3′) holds for every Fermat variety, for every product of Fermat varieties, and for every variety that such a product dominates.
- *Theorem F.* In a split Weil family, the loci Σ_d where the Weil classes have algebraic representatives of degree at most d are Zariski closed. The paper also gives a criterion, through the André–Oort theorem, for Σ to be the whole family.
- *Theorem G.* A new proof, by twisted cohomology on the symmetric product, of Schoen's theorem that the Prym variety B of an étale cyclic triple cover carries algebraic Weil classes. Schoen's subvariety Y has class c·η^n + w, with c > 0 and w ≠ 0, at members with maximal Hodge group.
- A transfer theorem for Weil classes along Prym varieties (Theorem 6.11), and Lemma 6.10, which shows that E^k × Ē^k is of split Weil type.
- *Proposition 6.15.* Prym varieties of cyclic triple covers, étale or branched, form families of dimension at most 3n. For n ≥ 4 they therefore miss the very general member of the split Weil family, which has dimension n².
- *Proposition 6.16.* The Abel–Prym curve of an étale cyclic triple cover deforms with its Prym variety B only along the Prym locus, although its class stays algebraic on the whole split Weil family. When the curve is embedded and B has maximal Hodge group, it is therefore not semiregular for n ≥ 4.
- *Proposition 6.17.* Up to an étale map, Schoen's subvariety Y is a component of the Prym–Brill–Noether locus: the line bundles M on the triple cover C with Nm M ≅ K_X and a nonzero section. It is smooth of dimension n at its general point, and its tangent space there is the annihilator of π\*H⁰(K_X) + s·H⁰(K_C − E). For étale double covers the same locus gives Mumford's Prym theta divisor, which deforms with every principally polarized abelian variety. So the analogues of Question 6.14 point both ways.

**Proved under a stated hypothesis**

- *Theorem E.* Assume (CM). This statement is claimed in an unrefereed preprint, and the paper uses it only as a hypothesis. Under it, HC holds for every Fermat variety, for their products, and for every variety they dominate.
- If Y is semiregular for one curve with maximal Hodge group, then every split Weil family over Q(√−3) of that dimension is Weil-algebraic.

**Not proved**

- HC itself.
- Each of (F2), (F3′), (L), (M), (V) and (IP).
- The semiregularity of Y in genus at least 5 (Question 6.14).
- HC for the Fermat fourfolds of degrees 110 and 220, the only degrees up to 250 that Theorems A and B, Peterson's theorem and Jumagulov's census leave open, and for Fermat varieties of most degrees divisible by 4.

## Where the conjecture stands after this paper

By Theorem C, HC comes down to (F2) and (F3′) together. Each has a first case that no known construction reaches:

- for (F2), the Weil classes of nonsplit abelian sixfolds and of abelian eightfolds, and the exceptional classes on the square of a Mumford fourfold;
- for (F3′), the square of a very general K3 surface with real multiplication by a real quadratic field, in a family of dimension 8 (some smaller families are settled by van Geemen–Schütt and by Varesco).

For the split Weil eightfolds over Q(√−3), three constructions were tested:

- *Prym varieties.* Proposition 6.15 shows they reach a family of dimension 12 inside one of dimension 16.
- *Products of Weil fourfolds.* Spreading them with Theorem F needs a uniform degree bound, and the natural cycles have unbounded degree (H8, Section 16, in `sources/H8`).
- *Schoen's subvariety Y.* It would have to deform in 4 directions beyond the Prym locus, which is Question 6.14. Proposition 6.17 identifies Y with a Prym–Brill–Noether locus, smooth at its general point; deciding the question needs its normal sheaf everywhere, including where h⁰ ≥ 2. Proposition 6.16 tests this on the Abel–Prym curve, which is built from the same map as Y: the curve does not deform in those directions. That does not decide the question for Y, since the theta divisor of a Jacobian, built from the same Abel–Jacobi map as the rigid Abel–Jacobi curve, deforms with every principally polarized abelian variety.

Closing any of these cases needs new algebraic cycles, and Section 8 of the paper says exactly what each would have to do.

## Layout

| Path | Contents |
|---|---|
| `paper/main.tex`, `paper/sections/` | LaTeX source (`amsart`). |
| `paper/references.bib` | Bibliography. Every entry was checked online (`verification/references/report.md`). |
| `paper/figures/*.png` | The five figures, at 300 dpi. |
| `paper/figures/src/` | TikZ sources of the figures. |
| `paper/main.pdf` | Compiled paper. |
| `scripts/build_paper.sh` | Builds the PDF, `tex.zip` and the arXiv tarball into `dist/`. |
| `verification/` | Machine checks of the finite steps (Appendix A of the paper). |
| `verification/{c,python,julia}/fermat114.*`, `verification/python/family1_symbolic.py` | Exact checks for degree 114: the characters α₁, α₂, the order parity ν₁₉, the weights of both families, and family I's residue. `python/fermat114.py --lattice` repeats the lattice computation [B₁₁₄ : S₁₁₄] without Aoki's theorem. |
| `verification/python/family2_certificate.py`, `family2_point.json` | The interval certificate of Appendix B (python-flint, Arb), run at 1000 and 600 bits. |
| `verification/lean-mathlib/FermatHodge/Degree114.lean` | Lean proofs of the finite and algebraic steps for degree 114. |
| `verification/lean-mathlib/` | Lean 4 proof, with Mathlib, of the classification behind Theorem B (15 files, about 3600 lines), including B₁,χ ≠ 0, and of the finite steps for degree 114. |
| `verification/{c,python,julia}/fermat_fourfolds.*` | Exhaustive search of the Hodge characters of Fermat surfaces and fourfolds of degree prime to 6. |
| `verification/{c,python,julia}/fermat_odd.*` | Exhaustive search of the Hodge characters of Fermat fourfolds of odd degree divisible by 3, with the moves of Section 3.7 and the identities of Lemma 3.26. |
| `sources/` | Earlier material imported from the author's working folder: the H8 project and the "Hodge Conjecture Full" drafts. It is kept for reference, and the paper does not depend on it. |

## Building

```sh
scripts/build_paper.sh          # needs pdflatex, bibtex, zip
```

This writes three files to `dist/`:

- `on-the-hodge-conjecture-for-fermat-varieties.pdf`
- `…-tex.zip`, the full source with the PNG figures
- `…-arxiv.tar.gz`, which contains `main.tex`, `sections/`, `main.bbl` and the PNG figures

The script reruns `pdflatex` until every cross-reference has settled. It also compiles the arXiv tarball with `pdflatex` alone before writing it.

## Machine checks

```sh
STRICT=1 verification/shell/run_all.sh
```

This needs python3, julia, a C99 compiler, lake (Lean 4) and Macaulay2. It runs the following:

- `closure_checks` in Python, Julia and C. All three use exact arithmetic, and they must print the same 218 lines.
- `lean/Closure.lean`, which uses Lean 4 core only, with no `sorry` and no `native_decide`. It prints the axioms of 20 main theorems, among them the six checks of the exceptional characters and their identities, and each uses only the standard axioms.
- The Macaulay2 scripts: Hodge numbers from the Jacobian ring, and Max Noether's theorem.
- `fermat_fourfolds` in Python, Julia and C up to degree 55, which must agree, and the C program up to degree 125 against `verification/c/fermat_fourfolds_125.expected`. Every Hodge quadruple contains a pair, and every Hodge sextuple contains a pair or is 5-standard.
- `fermat_odd` in Python, Julia and C up to degree 63, which must agree, and the C program up to degree 105 against `verification/c/fermat_odd_105.expected`. Every generating Hodge sextuple without a pair has a direct or a lowering move, or is one of the three exceptional characters.
- With `MATHLIB=1`, the Lean project in `verification/lean-mathlib` (Lean 4.34.1, Mathlib v4.34.1). It must build with no `sorry` and no `native_decide`, and `Axioms.lean` must show that its eighteen main theorems use only `propext`, `Classical.choice` and `Quot.sound`: eleven for the fourfold classification, among them `bernoulliNV` and the classification with it discharged, and seven for degree 114.

- The degree-114 checks: `fermat114` in Python, Julia and C, which must agree; the lattice computation; family I in sympy; and the interval certificate for family II at 1000 and 600 bits (needs python-flint and sympy).

`python3 verification/references/check_references.py` re-checks the bibliography online. Apart from Proposition 4.19, whose proof is the interval certificate, no proof in the paper depends on a computer.

## Citing

Zenodo archives every GitHub release under its own version DOI, and gathers all of them under one concept DOI.

| | DOI |
| --- | --- |
| all versions (concept DOI) | [10.5281/zenodo.23234362](https://doi.org/10.5281/zenodo.23234362) |
| release v1.4.0 (version DOI) | [10.5281/zenodo.23288228](https://doi.org/10.5281/zenodo.23288228) |
| release v1.3.0 (version DOI) | [10.5281/zenodo.23272887](https://doi.org/10.5281/zenodo.23272887) |
| release v1.2.0 (version DOI) | [10.5281/zenodo.23272739](https://doi.org/10.5281/zenodo.23272739) |
| release v1.1.0 (version DOI) | [10.5281/zenodo.23271115](https://doi.org/10.5281/zenodo.23271115) |
| release v1.0.2 (version DOI) | [10.5281/zenodo.23236587](https://doi.org/10.5281/zenodo.23236587) |
| release v1.0.1 (version DOI) | [10.5281/zenodo.23234501](https://doi.org/10.5281/zenodo.23234501) |
| release v1.0.0 (version DOI) | [10.5281/zenodo.23234363](https://doi.org/10.5281/zenodo.23234363) |

Cite the version DOI of the release you used, or the concept DOI for the work as a whole. `CITATION.cff` holds the same data.

## Note on preparation

The paper and the code were prepared with substantial help from an AI assistant, working under the author's direction; the author is responsible for the content. Section 8 of the paper lists the ideas the assistant proposed, as the policy of journals such as the Annals of Mathematics asks.

## License

MIT (see `LICENSE`).
