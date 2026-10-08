# When is every rational Hodge class algebraic?

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23234362.svg)](https://doi.org/10.5281/zenodo.23234362)

**Deep Bhattacharjee**
Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

This repository holds a 30-page paper in `amsart`, its LaTeX source with the figures as PNG, and the code that re-checks its finite steps in Python, Julia, C, Lean 4 and Macaulay2.

## The question

A rational Hodge class on a smooth complex projective variety is *algebraic* if it is a rational combination of classes of subvarieties. The Hodge conjecture says every rational Hodge class is algebraic. The literature has isolated several statements that would imply it. The paper asks which combinations of them do, and proves what the answer allows.

## Results

**Proved without hypothesis**

- *Theorem A.* The Hodge conjecture (HC) is equivalent to each of the following:
  - (F2) ∧ (F3′)
  - (L) ∧ (F3′)
  - (V) ∧ (F3′)
  - (CM) ∧ (IP) ∧ (F3′)
  - (L) ∧ (M)

  Here (F2) is HC for abelian varieties, (F3′) is HC modulo abelian varieties, (L) is the Lefschetz standard conjecture, (M) says every Hodge class is motivated, (V) is the variational Hodge conjecture, (CM) is HC for abelian varieties of CM type, and (IP) is propagation of algebraic classes from CM points.
- *Theorem B.* These are all the routes. Every set of the statements from which HC follows implies (F2) and (F3′). The only way to avoid assuming both is the pair (L) ∧ (M), which is equivalent to HC.
- *Theorem C.* (F3′) holds for every Fermat variety, for every product of Fermat varieties, and for every variety that such a product dominates.
- *Theorem D.* In a split Weil family, the loci Σ_d where the Weil classes have algebraic representatives of degree at most d are Zariski closed. The paper also gives a criterion, through the André–Oort theorem, for Σ to be the whole family.
- *Theorem E.* A new proof, by twisted cohomology on the symmetric product, of Schoen's theorem that the Prym variety B of an étale cyclic triple cover carries algebraic Weil classes. Schoen's subvariety Y has class c·η^n + w, with c > 0 and w ≠ 0, at members with maximal Hodge group.
- A transfer theorem for Weil classes along Prym varieties, and Lemma 5.10, which shows that E^k × Ē^k is of split Weil type.
- *Proposition 5.15.* Prym varieties of cyclic triple covers, étale or branched, form families of dimension at most 3n. For n ≥ 4 they therefore miss the very general member of the split Weil family, which has dimension n².

**Proved under a stated hypothesis**

- Assume (CM). This statement is claimed in an unrefereed preprint, and the paper uses it only as a hypothesis. Under it, HC holds for every Fermat variety, for their products, and for every variety they dominate.
- If Y is semiregular for one curve with maximal Hodge group, then every split Weil family over Q(√−3) of that dimension is Weil-algebraic.

**Not proved**

- HC itself.
- Each of (F2), (F3′), (L), (M), (V) and (IP).
- The semiregularity of Y in genus at least 5 (Question 5.14).

## Where the conjecture stands after this paper

By Theorem A, HC comes down to (F2) and (F3′) together. Each has a first case that no known construction reaches:

- for (F2), the Weil classes of nonsplit abelian sixfolds and of abelian eightfolds, and the exceptional classes on the square of a Mumford fourfold;
- for (F3′), the square of a K3 surface with real multiplication.

For the split Weil eightfolds over Q(√−3), three constructions were tested:

- *Prym varieties.* Proposition 5.15 shows they reach a family of dimension 12 inside one of dimension 16.
- *Products of Weil fourfolds.* Spreading them with Theorem D needs a uniform degree bound, and the natural cycles have unbounded degree (H8, Section 16, in `sources/H8`).
- *Schoen's subvariety Y.* It would have to deform in 4 directions beyond the Prym locus, which is Question 5.14.

Closing any of these cases needs new algebraic cycles, and Section 7 of the paper says exactly what each would have to do.

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
- `…-arxiv.tar.gz`, which contains `main.tex`, `sections/`, `main.bbl` and the PNG figures

The script reruns `pdflatex` until every cross-reference has settled. It also compiles the arXiv tarball with `pdflatex` alone before writing it.

## Machine checks

```sh
STRICT=1 verification/shell/run_all.sh
```

This needs python3, julia, a C99 compiler, lake (Lean 4) and Macaulay2. It runs the following:

- `closure_checks` in Python, Julia and C. All three use exact arithmetic, and they must print the same 207 lines.
- `lean/Closure.lean`, which uses Lean 4 core only, with no `sorry` and no `native_decide`. It prints the axioms of 12 main theorems, and each uses only the standard axioms.
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
