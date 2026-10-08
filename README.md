# When is every rational Hodge class algebraic?

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23234362.svg)](https://doi.org/10.5281/zenodo.23234362)

**Deep Bhattacharjee**
Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

This repository holds the LaTeX source of the paper (`amsart`, figures as PNG), the compiled PDF, and the code that re-checks the paper's finite steps in Python, Julia, C, Lean 4 and Macaulay2.

## What the paper proves, and what it does not

**The Hodge conjecture is not proved here.** The paper asks which of the standard statements around the rational Hodge conjecture it follows from, proves what that answer allows, and stops at the first statement on each route that it cannot prove.

**Proved without hypothesis**

- *Theorem A.* The Hodge conjecture (HC) is equivalent to each of the following:
  - (F2) ∧ (F3′)
  - (L) ∧ (F3′)
  - (V) ∧ (F3′)
  - (CM) ∧ (IP) ∧ (F3′)
  - (L) ∧ (M)
- *Theorem B.* These are all the routes. Every set of the statements from which HC follows implies (F2) and (F3′). The only way to avoid assuming both is the pair (L) ∧ (M), and that pair is equivalent to HC.
- *Theorem C.* (F3′) holds for every Fermat variety, for every product of Fermat varieties, and for every variety that such a product dominates.
- *Theorem D.* In a split Weil family, the loci Σ_d where the Weil classes have algebraic representatives of degree at most d are Zariski closed. The paper also gives the André–Oort criterion for Σ = S.
- *Theorem E.* This is a new proof, by twisted cohomology on the symmetric product, of Schoen's theorem that the Prym variety B of an étale cyclic triple cover carries algebraic Weil classes. Schoen's subvariety Y has class c·η^n + w, with c > 0 and w ≠ 0, at members with maximal Hodge group.
- A transfer theorem for Weil classes along Prym varieties, and Lemma 5.10, which shows that E^k × Ē^k is of split Weil type.

**Proved under a stated hypothesis**

- Assume (CM), the Hodge conjecture for CM abelian varieties. That statement is claimed in an unrefereed preprint, and the paper uses it only as a hypothesis. Under it, HC holds for every Fermat variety, for their products, and for every variety they dominate.
- If Y is semiregular for one curve with maximal Hodge group, then every split Weil family over Q(√−3) of that dimension is Weil-algebraic.

**Not proved**

- HC itself.
- Each of (F2), (F3′), (L), (M), (V) and (IP).
- The semiregularity of Y in genus at least 5 (Question 5.14).

Section 7 of the paper names the first open cases.

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
| `sources/` | Earlier material imported from the author's working folder: the H8 project and the "Hodge Conjecture Full" drafts. It is kept for reference, and the paper does not depend on it. |

## Building

```sh
scripts/build_paper.sh          # needs pdflatex, bibtex, zip
```

This writes three files to `dist/`:

- `when-is-every-rational-hodge-class-algebraic.pdf`
- `…-tex.zip`, the full source with the PNG figures
- `…-arxiv.tar.gz`, which contains `main.tex`, `sections/`, `main.bbl` and the PNG figures. The script compiles it with `pdflatex` alone before writing it.

## Machine checks

```sh
STRICT=1 verification/shell/run_all.sh
```

This needs python3, julia, a C99 compiler, lake (Lean 4) and Macaulay2. It runs the following:

- `closure_checks` in Python, Julia and C. All three are exact, and they must print the same 196 lines.
- `lean/Closure.lean`, which uses Lean 4 core only, with no `sorry` and no `native_decide`.
- The Macaulay2 scripts: Hodge numbers from the Jacobian ring, and Max Noether's theorem.

`python3 verification/references/check_references.py` re-checks the bibliography online. No proof in the paper depends on a computer.

## Citing

Zenodo archives every GitHub release under its own version DOI, and gathers all of them under one concept DOI.

| | DOI |
| --- | --- |
| all versions (concept DOI) | [10.5281/zenodo.23234362](https://doi.org/10.5281/zenodo.23234362) |
| release v1.0.1 (version DOI) | [10.5281/zenodo.23234501](https://doi.org/10.5281/zenodo.23234501) |
| release v1.0.0 (version DOI) | [10.5281/zenodo.23234363](https://doi.org/10.5281/zenodo.23234363) |

Cite the version DOI of the release you used, or the concept DOI for the work as a whole. `CITATION.cff` holds the same data.

## Note on preparation

Parts of the paper and of the code were drafted with the help of an AI assistant, working under the author's direction. Responsibility for the content rests with the author.

## License

MIT (see `LICENSE`).
