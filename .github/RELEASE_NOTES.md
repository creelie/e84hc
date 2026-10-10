**When is every rational Hodge class algebraic?**
Deep Bhattacharjee. Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

The paper determines which combinations of the standard statements around the rational Hodge conjecture imply it. Every such combination contains the conjecture modulo abelian varieties, unless it contains both the Lefschetz standard conjecture and André's conjecture that every Hodge class is motivated, a pair equivalent to the Hodge conjecture itself.

Granting the recently claimed Hodge conjecture for CM abelian varieties, it proves the conjecture for every Fermat variety and reduces the abelian case to propagation from CM points. For Weil classes it proves a criterion by bounded degree at CM points. It also extracts from Schoen's cycles one subvariety whose semiregularity would settle the split Weil families over Q(√−3) in every dimension.

Without any hypothesis, it proves the Hodge conjecture for Fermat fourfolds of every odd degree (Theorem F).

**The Hodge conjecture itself is not proved.** Section 7 of the paper lists what is proved, what is proved under a stated hypothesis, and what remains open.

### Files

- `when-is-every-rational-hodge-class-algebraic.pdf`: the paper, 49 pages, `amsart`.
- `when-is-every-rational-hodge-class-algebraic-tex.zip`: the full LaTeX source, with the figures as PNG and their TikZ sources.
- `when-is-every-rational-hodge-class-algebraic-arxiv.tar.gz`: the arXiv submission, containing `main.tex`, `sections/`, `main.bbl` and the PNG figures. It compiles with pdflatex alone.

The workflow attaches these files to the release once the paper has been built on GitHub.

### Checks

`verification/shell/run_all.sh` re-runs the finite steps:

- `closure_checks` in Python, Julia and C, in exact arithmetic, with identical 218-line outputs;
- a Lean 4 file that uses the core library only, with no `sorry` and no `native_decide`;
- a Lean 4 project with Mathlib (`verification/lean-mathlib`) that proves the classification of Hodge characters behind Theorem F, including B₁,χ ≠ 0; its main theorems use only the standard axioms;
- exhaustive searches of the Hodge characters of Fermat surfaces and fourfolds of degree prime to 6, and of Fermat fourfolds of odd degree divisible by 3, in C, Python and Julia;
- Macaulay2 scripts for the Jacobian-ring Hodge numbers and Max Noether's theorem.

All 77 references were checked online. No proof in the paper depends on a computer.

### Citation and DOI

Concept DOI, covering all versions: [10.5281/zenodo.23234362](https://doi.org/10.5281/zenodo.23234362). Zenodo gives each release its own version DOI under it: v1.0.0 is [10.5281/zenodo.23234363](https://doi.org/10.5281/zenodo.23234363), v1.0.1 is [10.5281/zenodo.23234501](https://doi.org/10.5281/zenodo.23234501), v1.0.2 is [10.5281/zenodo.23236587](https://doi.org/10.5281/zenodo.23236587) and v1.1.0 is [10.5281/zenodo.23271115](https://doi.org/10.5281/zenodo.23271115).

### What is new in this version

- Theorem F now covers every odd degree m. A new subsection, Section 3.7, treats odd m divisible by 3. Every Hodge sextuple that generates Z/m and contains no pair a, −a has a move: one of Aoki's cycles trades it for a quadruple, whose classes are known, or for a sextuple of smaller orders. The only exceptions are three characters, in degrees 21, 33 and 39 (Theorem 3.27). Identities on the Fermat fourfolds of degrees 21, 66 and 78 close them (Lemma 3.26). The proof is by hand.
- The theorem is new for the odd degrees m > 199 that are divisible by 3 or 5 and have a prime factor larger than 7. The first are 201, 205, 207, 213 and 215. Remark 3.7 now also cites Aoki's 2000 theorem on abelian varieties of Fermat type and Peterson's 2026 preprint on degrees 2^a 3^b 5^c 7^d.
- New checks:
  - `fermat_odd` in Python, Julia and C lists every Hodge sextuple in odd degrees divisible by 3 and finds a move for each. The three programs agree up to degree 63, and the C program reaches degree 105.
  - `Closure.lean` checks the three exceptional characters and their identities by `decide`.
  - The induction itself is not formalized in Lean.
- Section 7 cites Varesco's theorem (Math. Z. 2023) for the general member of the first four-dimensional families of K3 surfaces with real multiplication, next to the families of van Geemen and Schütt.
- The reference checker also asks the Japan Link Center, and all 77 references verify.
- v1.1.1 recorded the version DOI of v1.1.0 and left the paper unchanged.

### What v1.1.0 added

- Theorem F: the Hodge conjecture holds for the Fermat fourfold of every degree m prime to 6. The proof shows that every Hodge character contains two entries a and −a, or is (x, x+m/5, x+2m/5, x+3m/5, x+4m/5, −5x) up to order (Theorem 3.9). Classes of the first kind come from linear subspaces through Shioda and Ran's inductive structure, and those of the second kind from Aoki's cycles, pulled back along a covering of Fermat fourfolds. The only analytic input is B₁,χ ≠ 0 for odd primitive characters χ.
- The theorem is new when 5 divides m, m > 199 and m is not a power of 5 (first cases 205, 215, 235). Smaller degrees were settled by computer searches, and other degrees prime to 6 by Aoki. Remark 3.21 shows that a step in Kang's proof of the general statement fails.
- The classification is proved in Lean 4 with Mathlib, and so is B₁,χ ≠ 0, derived from Mathlib's L(1, χ) ≠ 0 through the Gauss sum and the logarithmic series. Only the geometric input stays a hypothesis there. The classification is also re-checked by exhaustive search up to degree 125.
- Section 7 now describes the first open case of (F3′) precisely: the square of a very general K3 surface with real multiplication, whose maximal families have Picard number 2 and dimension 8.

Sections 2 and 4 to 6 are unchanged from v1.0.2.
