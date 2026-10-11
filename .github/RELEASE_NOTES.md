**On the Hodge conjecture for Fermat varieties**
Deep Bhattacharjee. Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

The paper proves the Hodge conjecture for the Fermat varieties of degrees 44, 52 and 114 in every dimension, and more generally of every degree 2^a 11^b, every degree 2^a 13^b and every degree 2^a 3^b 19^c with a ≤ 1, together with their products and the abelian varieties of Fermat type of these degrees (Theorem A). For the degrees divisible by 44 (44, 88, 176, 352, 484, …) or by 52 (52, 104, 208, 416, 676, …) the theorem had not been proved before; the 2026 preprint of Miranda, Movasati, Rufino and Villaflor treats every degree below 65 except 44, 51 and 52. For the degrees divisible by 57 it is the first proof that does not rest on a statement of Kang whose proof has a gap; the only earlier argument, for degree 57, does. For 114, 171, 342, 513, … the theorem had not been stated before. Four steps, the nonvanishing of four residues (Propositions 4.20, 4.23, 4.26 and 4.28), are certified computations in interval arithmetic; everything else is proved by hand.

It also proves the Hodge conjecture for Fermat fourfolds of every odd degree (Theorem B), determines which combinations of the standard statements around the Hodge conjecture imply it (Theorems C and D), and proves the conditional and partial results of earlier versions (Theorems E, F and G).

**The Hodge conjecture itself is not proved.** Section 8 of the paper lists what is proved, what is proved under a stated hypothesis, and what remains open.

### Files

- `on-the-hodge-conjecture-for-fermat-varieties.pdf`: the paper, 72 pages, `amsart`.
- `on-the-hodge-conjecture-for-fermat-varieties-tex.zip`: the full LaTeX source, with the figures as PNG and their TikZ sources.
- `on-the-hodge-conjecture-for-fermat-varieties-arxiv.tar.gz`: the arXiv submission, containing `main.tex`, `sections/`, `main.bbl` and the PNG figures. It compiles with pdflatex alone.

The workflow attaches these files to the release once the paper has been built on GitHub.

### Checks

`verification/shell/run_all.sh` re-runs the finite steps:

- `closure_checks` in Python, Julia and C, in exact arithmetic, with identical 218-line outputs;
- a Lean 4 file that uses the core library only, with no `sorry` and no `native_decide`;
- a Lean 4 project with Mathlib (`verification/lean-mathlib`) that proves the classification of Hodge characters behind Theorem B, including B₁,χ ≠ 0, and the finite and algebraic steps for degrees 114, 44 and 52; its 31 main theorems use only the standard axioms;
- exhaustive searches of the Hodge characters of Fermat surfaces and fourfolds, in C, Python and Julia;
- `fermat114` in Python, Julia and C, the lattice computation of [B₁₁₄ : S₁₁₄], family I in sympy, and the Arb certificate for family II at 1000 and 600 bits;
- `fermat44` in Python, Julia and C, with identical 14-line outputs, the lattice computation B₄₄ = S₄₄ + Z[β], the Arb certificate for the family of degree 11 at 1000 and 600 bits, and a contour integral that reproduces its residue to 15 digits;
- `fermat52` in Python, Julia and C, with identical 20-line outputs, the lattice computation B₅₂ = S₅₂ + Z[β], the Arb certificates for the families of degrees 14 and 5 at 1000 and 600 bits, and contour integrals that reproduce both residues to 15 digits;
- Macaulay2 scripts for the Jacobian-ring Hodge numbers and Max Noether's theorem.

All 86 references were checked online: 85 against an online record, and one public repository by hand.

### Citation and DOI

Concept DOI, covering all versions: [10.5281/zenodo.23234362](https://doi.org/10.5281/zenodo.23234362). Zenodo gives each release its own version DOI under it: v1.0.0 is [10.5281/zenodo.23234363](https://doi.org/10.5281/zenodo.23234363), v1.0.1 is [10.5281/zenodo.23234501](https://doi.org/10.5281/zenodo.23234501), v1.0.2 is [10.5281/zenodo.23236587](https://doi.org/10.5281/zenodo.23236587), v1.1.0 is [10.5281/zenodo.23271115](https://doi.org/10.5281/zenodo.23271115), v1.2.0 is [10.5281/zenodo.23272739](https://doi.org/10.5281/zenodo.23272739), v1.3.0 is [10.5281/zenodo.23272887](https://doi.org/10.5281/zenodo.23272887), v1.4.0 is [10.5281/zenodo.23288228](https://doi.org/10.5281/zenodo.23288228), v1.5.0 is [10.5281/zenodo.23289125](https://doi.org/10.5281/zenodo.23289125) and v1.6.0 is [10.5281/zenodo.23289930](https://doi.org/10.5281/zenodo.23289930).

### What is new in this version

- Theorem A now also covers every degree 2^a 13^b. In degree 52 Aoki's reduction leaves one class, a balanced multiset β of ten residues with exactly one residue of order 13 (Corollary 4.5, which now treats 44, 52 and 114 together). An enumeration shows that no balanced multiset of four or six residues modulo 52 has an odd number of residues of order 13, and a lattice computation gives B₅₂ = S₅₂ + Z[β] without Aoki's theorem.
- β is the join of the threefold characters α = (1, 5, 16, 37, 45) and α′ = (29, 18, 42, 50, 17), whose types are complementary for every unit (Lemma 4.25). Both pieces of H³ need families of curves.
- A block family of degree 14 for α (Proposition 4.26, Corollary 4.27) and one of degree 5 for 9α′ = (1, 6, 14, 34, 49) (Proposition 4.28, Corollary 4.29) have nonzero residues, certified in Arb (Appendix B). Remark 4.32 records what was known: Aoki covers the degrees 2^a 13^b not divisible by 52, and the preprint of Miranda, Movasati, Rufino and Villaflor excludes 52.
- New checks: `fermat52` in Python, Julia and C, `Degree52.lean` (seven more theorems in `Axioms.lean`), `family52_certificate.py` and `family52_contour.py`.

### What v1.5.0 added (numbering as in v1.5.0)

- Theorem A now also covers every degree 2^a 11^b. In degree 44 Aoki's reduction leaves one class, a balanced multiset β of eight residues with exactly one residue of order 11 (Corollary 4.5, which now treats 44 and 114 together). An enumeration shows that no balanced multiset of four or six residues modulo 44 has this property, so β is the first class in degree 44 that linear subspaces and Aoki's cycles miss.
- β is the join of the threefold character α = (1, 5, 8, 33, 41) and the curve character b = (9, 37, 42), whose types are complementary for every unit (Lemma 4.22). Proposition 4.18 joins a threefold character that is carried by curves with any curve character of complementary type, through the Lefschetz (1,1) theorem on a product of two curves and Shioda's inductive structure with r = 4, s = 2.
- A block family of degree 11 for α (Proposition 4.23, Corollary 4.24) has a nonzero residue, certified in Arb (Appendix B). Remark 4.26 records what was known: Aoki covers the degrees 2^a 11^b not divisible by 44, and the preprint of Miranda, Movasati, Rufino and Villaflor excludes 44.
- New checks: `fermat44` in Python, Julia and C, `Degree44.lean`, `family44_certificate.py` and `family44_contour.py`.

### What v1.4.0 added (numbering as in v1.4.0)

- A new Section 4 proves Theorem A. Aoki's reduction leaves one class in degree 114, a balanced multiset of ten residues with one residue of order 19 (Corollary 4.5). It is the join of two characters of the Fermat threefold of degree 114 with complementary level-one Hodge structures (Lemma 4.6). Each is shown to be carried by curves through a residue formula for the derivative of the Abel–Jacobi map of a family of curves, which extends Peterson's method to "block families" (Theorem 4.16). The family for the first character, of cubic forms, is computed by hand (Proposition 4.18); the family for the second has degree 24 and is certified in Arb (Proposition 4.19, Appendix B).
- The paper is reframed around this theorem: new title, abstract and introduction, with the main theorems relettered A to G. Section 8 now says which ideas came from the AI assistant and where, as the Annals of Mathematics policy asks.
- Remark 4.21 places the theorem: the even-degree census of Fermat fourfolds up to 250 now leaves only the degrees 110 and 220 open.
- Eight references were added, all verified online.

### What v1.3.0 added

- Proposition 6.17 (5.17 in v1.3.0) describes Schoen's subvariety Y as a component of a Prym–Brill–Noether locus, smooth of dimension n at its general point; for étale double covers the same locus gives Mumford's Prym theta divisor. Question 6.14 stays open.

### What v1.2.0 added (its Theorem F is Theorem B now, and its Sections 4 to 7 are Sections 5 to 8)

- Theorem F now covers every odd degree m. A new subsection, Section 3.7, treats odd m divisible by 3. Every Hodge sextuple that generates Z/m and contains no pair a, −a has a move: one of Aoki's cycles trades it for a quadruple, whose classes are known, or for a sextuple of smaller orders. The only exceptions are three characters, in degrees 21, 33 and 39 (Theorem 3.27). Identities on the Fermat fourfolds of degrees 21, 66 and 78 close them (Lemma 3.26). The proof is by hand.
- The theorem is new for the odd degrees m > 199 that are divisible by 3 or 5 and have a prime factor larger than 7. The first are 201, 205, 207, 213 and 215. Remark 3.7 now also cites Aoki's 2000 theorem on abelian varieties of Fermat type and Peterson's 2026 preprint on degrees 2^a 3^b 5^c 7^d.
- New checks:
  - `fermat_odd` in Python, Julia and C lists every Hodge sextuple in odd degrees divisible by 3 and finds a move for each. The three programs agree up to degree 63, and the C program reaches degree 105.
  - `Closure.lean` checks the three exceptional characters and their identities by `decide`.
  - The induction itself is not formalized in Lean.
- Section 7 cites Varesco's theorem (Math. Z. 2023) for the general member of the first four-dimensional families of K3 surfaces with real multiplication, next to the families of van Geemen and Schütt.
- The reference checker also asks the Japan Link Center, and all 77 references verify.

### What v1.1.0 added

- Theorem F: the Hodge conjecture holds for the Fermat fourfold of every degree m prime to 6. The proof shows that every Hodge character contains two entries a and −a, or is (x, x+m/5, x+2m/5, x+3m/5, x+4m/5, −5x) up to order (Theorem 3.9). Classes of the first kind come from linear subspaces through Shioda and Ran's inductive structure, and those of the second kind from Aoki's cycles, pulled back along a covering of Fermat fourfolds. The only analytic input is B₁,χ ≠ 0 for odd primitive characters χ.
- The theorem is new when 5 divides m, m > 199 and m is not a power of 5 (first cases 205, 215, 235). Smaller degrees were settled by computer searches, and other degrees prime to 6 by Aoki. Remark 3.21 shows that a step in Kang's proof of the general statement fails.
- The classification is proved in Lean 4 with Mathlib, and so is B₁,χ ≠ 0, derived from Mathlib's L(1, χ) ≠ 0 through the Gauss sum and the logarithmic series. Only the geometric input stays a hypothesis there. The classification is also re-checked by exhaustive search up to degree 125.
- Section 7 now describes the first open case of (F3′) precisely: the square of a very general K3 surface with real multiplication, whose maximal families have Picard number 2 and dimension 8.

Sections 2 and 4 to 6 are unchanged from v1.0.2.
