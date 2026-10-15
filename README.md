# On the Hodge conjecture for Fermat varieties

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23234362.svg)](https://doi.org/10.5281/zenodo.23234362)

**Deep Bhattacharjee**
Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

This repository holds an 83-page paper in `amsart`, its LaTeX source with the figures as PNG, and the code that re-checks its finite steps in Python, Julia, C, Lean 4 (with and without Mathlib) and Macaulay2.

## Main result

**Theorem A.** Let m = 2^a·3^b·19^c or m = 2^a·3^b·17^c with a ≤ 1, or m = 2^a·3^b·11^c, or m = 2^a·3^b·13^c. Then the Hodge conjecture holds for the Fermat variety x₀^m + … + x_{n+1}^m = 0 of every dimension n, for every product of Fermat varieties of degree m, and for every abelian variety of Fermat type of degree m.

In particular the Hodge conjecture holds for the Fermat varieties of degrees 33, 39, 44, 51, 52 and 114 in every dimension. When none of 57, 44, 52, 51, 33 and 39 divides m the theorem is Aoki's. For 44 | m, 52 | m and 51 | m it had not been proved before: the 2026 preprint of Miranda, Movasati, Rufino and Villaflor treats every degree below 65 except 44, 51 and 52, and the degrees 44, 88, 176, 352, 484, …, 52, 104, 208, 416, 676, … and 51, 102, 153, 306, 459, … appear here for the first time (Remarks 4.46, 4.47 and 4.48). For 57 | m the only earlier argument is in that preprint: it states the case m = 57, which by Aoki's reduction gives the others, but it ends with a statement of Kang about the Fermat fourfold of degree 114 whose proof has a gap (Remark 3.21). The proof here does not use Kang's statement, so for 57 | m it is the first complete proof, and for 114, 171, 342, 513, … the theorem had not been stated before. The same holds for 33 and 39, which that preprint also reaches through Kang's statement; the degrees 66, 78, 99, 117, 132, 156, … divisible by 33 or 39 are stated here for the first time (Remark 4.49). It does not use OpenAI's unrefereed claim of the Hodge conjecture for CM abelian varieties either, which would give every Fermat variety (Theorem E).

How it works (Section 4):

- Aoki's reduction leaves one class in degree 114: a balanced multiset β of ten residues with exactly one residue of order 19, which linear subspaces and Aoki's cycles cannot reach (Lemma 4.3, Corollary 4.6). In degree 44 it leaves one class as well, a multiset of eight residues with exactly one residue of order 11, in degree 52 a multiset of ten residues with exactly one residue of order 13, and in degree 51, at level 102, a multiset of ten residues with exactly one residue of order 17. In degrees 33 and 39 the class left is one of the exceptional characters O₃₃, O₃₉ of Section 3.7; it is detected by the parity of the number of its elements of square 1 (Lemma 4.4), and it is algebraic by the identities of Lemma 3.26.
- β is the join of two characters α₁, α₂ of the Fermat threefold of degree 114 whose Hodge structures in H³ have level one and complementary types (Lemma 4.7).
- **The coniveau step, by hand (Section 4.5).** Each of these pieces of H³ is supported on a divisor. The piece belongs to the quotient of the Fermat threefold by the kernel of the character, which is birational to a hypersurface in a torus with a simplex as Newton polytope. A *block pattern* (Definition 4.23), a small table of integers checked by hand, shows that the Fine interior of the polytope is empty (Lemma 4.24), so by Batyrev's criterion the quotient has negative Kodaira dimension, hence is uniruled by the minimal model program for threefolds, hence its H³ has coniveau one (Theorem 4.25). Corollary 4.28 lists a block pattern for each of the seven characters needed in degrees 114, 44, 52 and 51.
- The pieces are joined on a product of divisors by the Lefschetz (1,1) theorem and Deligne's description of classes supported on a divisor, and carried to the eightfold (or sixfold) by Shioda's inductive structure (Proposition 4.27).
- **No step of the proof of Theorem A uses a computer.**
- *A second proof of the coniveau step.* The same block patterns give families of curves on the threefold, and a residue formula for the derivative of their Abel–Jacobi maps, which extends Peterson's argument for degree 35 to "block families" (Theorem 4.17), shows that the pieces are carried by curves. One residue, for a family of cubic forms, is computed by hand (Proposition 4.29); the other six (Propositions 4.30, 4.33, 4.36, 4.38, 4.41 and 4.43) are certified in interval arithmetic in Arb (Appendix B). The proof of Theorem A does not use them.
- In degree 44 the class is the join of a character α = (1, 5, 8, 33, 41) of the Fermat threefold and a character b = (9, 37, 42) of the Fermat curve with complementary types (Lemma 4.32); in degree 52 of α = (1, 5, 16, 37, 45) and α′ = (29, 18, 42, 50, 17) (Lemma 4.35), with block patterns for α and 9α′ = (1, 6, 14, 34, 49); in degree 51, at level 102, of α = (1, 7, 51, 60, 85) and α′ = (91, 34, 26, 98, 57) (Lemma 4.40), with block patterns for 37α′ = (1, 34, 44, 56, 69) and 5α = (5, 35, 51, 96, 17). No balanced multiset of four or six residues modulo 44, 52 or 102 has an odd number of residues of order 11, 13 or 17.
- Degree 110 is different. In every pair of threefold characters that the searches found for the class left there, one character has a "shadow", a non-unit t with Σ⟨tα_k⟩ = m, which gives an interior lattice point of the polytope (Remark 4.26(b)). That character has no block pattern, and its quotient has nonnegative Kodaira dimension. Degree 110 stays open.

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
- HC for the Fermat fourfolds of degrees 110 and 220, the only degrees up to 250 that Theorems A and B, Peterson's theorem and Jumagulov's census leave open, and for Fermat varieties of most degrees divisible by 4 other than 2^a·3^b, 2^a·3^b·11^c and 2^a·3^b·13^c.

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
| `verification/python/family2_certificate.py`, `family2_point.json` | The interval certificate of Appendix B for the family of degree 24 (python-flint, Arb), run at 1000 and 600 bits. |
| `verification/{c,python,julia}/fermat44.*` | Exact checks for degree 44: the characters α and b, the order parity ν₁₁ on β and on the generators of S₄₄, the enumeration of the balanced multisets of four and six residues, and the weights of the family. `python/fermat44.py --lattice` checks B₄₄ = S₄₄ + Z[β] without Aoki's theorem. |
| `verification/python/family44_certificate.py`, `family44_point.json`, `family44_contour.py` | The interval certificate of Appendix B for the family of degree 11, run at 1000 and 600 bits, and an independent contour-integral check of its residue. |
| `verification/{c,python,julia}/fermat52.*` | Exact checks for degree 52: the characters α and α′, the order parity ν₁₃ on β and on the generators of S₅₂, the enumeration of the balanced multisets of four and six residues, and the weights of both families. `python/fermat52.py --lattice` checks B₅₂ = S₅₂ + Z[β] without Aoki's theorem. |
| `verification/python/family52_certificate.py`, `family52a_point.json`, `family52b_point.json`, `family52_contour.py` | The interval certificates of Appendix B for the families of degrees 14 and 5, run at 1000 and 600 bits, and an independent contour-integral check of both residues. |
| `verification/{c,python,julia}/fermat51.*` | Exact checks for degree 51 at level 102: the characters α and α′, the order parity ν₁₇ on β and on the generators of S₁₀₂, the enumeration of the balanced multisets of four and six residues, and the weights of both families. `python/fermat51.py --lattice` checks B₁₀₂ = S₁₀₂ + Z[β] without Aoki's theorem. |
| `verification/python/family51_certificate.py`, `family51a_point.json`, `family51b_point.json`, `family51_contour.py` | The interval certificates of Appendix B for the families of degrees 6 and 18, run at 1000 and 600 bits, and an independent contour-integral check of both residues. |
| `verification/lean-mathlib/FermatHodge/Degree114.lean`, `Degree44.lean`, `Degree52.lean`, `Degree51.lean` | Lean proofs of the finite and algebraic steps for degrees 114, 44, 52 and 51. |
| `verification/{c,python,julia}/patterns.*`, `verification/lean-mathlib/FermatHodge/Patterns.lean` | The block patterns of Corollary 4.28, and the homomorphism ν_R of Lemma 4.4 at levels 33 and 39. |
| `verification/lean-mathlib/` | Lean 4 proof, with Mathlib, of the classification behind Theorem B, including B₁,χ ≠ 0, and of the finite steps for degrees 114, 44, 52 and 51, 33 and 39 (22 files, about 4300 lines). |
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
- With `MATHLIB=1`, the Lean project in `verification/lean-mathlib` (Lean 4.34.1, Mathlib v4.34.1). It must build with no `sorry` and no `native_decide`, and `Axioms.lean` must show that its forty-five main theorems use only `propext`, `Classical.choice` and `Quot.sound`: eleven for the fourfold classification, among them `bernoulliNV` and the classification with it discharged, seven for degree 114, six for degree 44, seven for degree 52, seven for degree 51, and seven for the block patterns and the degrees 33 and 39.

- The degree-114 checks: `fermat114` in Python, Julia and C, which must agree; the lattice computation; family I in sympy; and the interval certificate for family II at 1000 and 600 bits (needs python-flint and sympy).
- The degree-44 checks: `fermat44` in Python, Julia and C, which must agree; the lattice computation; the interval certificate at 1000 and 600 bits; and the contour integral (needs python-flint and mpmath).
- The degree-52 checks: `fermat52` in Python, Julia and C, which must agree; the lattice computation; both interval certificates at 1000 and 600 bits; and the contour integrals (needs python-flint and mpmath).
- The degree-51 checks: `fermat51` in Python, Julia and C, which must agree; the lattice computation at level 102; both interval certificates at 1000 and 600 bits; and the contour integrals (needs python-flint and mpmath).
- `patterns` in Python, Julia and C, which must print the same 10 lines: the seven block patterns of Corollary 4.28, conditions (P1) to (P3), and, for 33 and 39, the elements of square 1, ν_R(O_M) = 1 and ν_R = 0 on the pairs and standard multisets.

`python3 verification/references/check_references.py` re-checks the bibliography online. Apart from Propositions 4.30, 4.33, 4.36, 4.38, 4.41 and 4.43, whose proofs are the interval certificates and which the proof of Theorem A does not use, no proof in the paper depends on a computer.

## Citing

Zenodo archives every GitHub release under its own version DOI, and gathers all of them under one concept DOI.

| | DOI |
| --- | --- |
| all versions (concept DOI) | [10.5281/zenodo.23234362](https://doi.org/10.5281/zenodo.23234362) |
| release v1.8.0 (version DOI) | [10.5281/zenodo.23401546](https://doi.org/10.5281/zenodo.23401546) |
| release v1.7.0 (version DOI) | [10.5281/zenodo.23292094](https://doi.org/10.5281/zenodo.23292094) |
| release v1.6.0 (version DOI) | [10.5281/zenodo.23289930](https://doi.org/10.5281/zenodo.23289930) |
| release v1.5.0 (version DOI) | [10.5281/zenodo.23289125](https://doi.org/10.5281/zenodo.23289125) |
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
