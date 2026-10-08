**When is every rational Hodge class algebraic?**
Deep Bhattacharjee. Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

The paper determines which combinations of the standard statements around the rational Hodge conjecture imply it. Every such combination contains the conjecture modulo abelian varieties, unless it contains both the Lefschetz standard conjecture and André's conjecture that every Hodge class is motivated, a pair equivalent to the Hodge conjecture itself.

Granting the recently claimed Hodge conjecture for CM abelian varieties, it proves the conjecture for every Fermat variety and reduces the abelian case to propagation from CM points. For Weil classes it proves a criterion by bounded degree at CM points. It also extracts from Schoen's cycles one subvariety whose semiregularity would settle the split Weil families over Q(√−3) in every dimension.

**The Hodge conjecture itself is not proved.** Section 7 of the paper lists what is proved, what is proved under a stated hypothesis, and what remains open.

### Files

- `when-is-every-rational-hodge-class-algebraic.pdf`: the paper, 32 pages, `amsart`.
- `when-is-every-rational-hodge-class-algebraic-tex.zip`: the full LaTeX source, with the figures as PNG and their TikZ sources.
- `when-is-every-rational-hodge-class-algebraic-arxiv.tar.gz`: the arXiv submission, containing `main.tex`, `sections/`, `main.bbl` and the PNG figures. It compiles with pdflatex alone.

The workflow attaches these files to the release once the paper has been built on GitHub.

### Checks

`verification/shell/run_all.sh` re-runs the finite steps:

- `closure_checks` in Python, Julia and C, in exact arithmetic, with identical 218-line outputs;
- a Lean 4 file that uses the core library only, with no `sorry` and no `native_decide`;
- Macaulay2 scripts for the Jacobian-ring Hodge numbers and Max Noether's theorem.

All 62 references were checked online. No proof in the paper depends on a computer.

### Citation and DOI

Concept DOI, covering all versions: [10.5281/zenodo.23234362](https://doi.org/10.5281/zenodo.23234362). Zenodo gives each release its own version DOI under it: v1.0.0 is [10.5281/zenodo.23234363](https://doi.org/10.5281/zenodo.23234363) and v1.0.1 is [10.5281/zenodo.23234501](https://doi.org/10.5281/zenodo.23234501).

### What is new in this version

- Proposition 5.15: Prym varieties of cyclic triple covers, étale or branched, form families of dimension at most 3n, so for n ≥ 4 they miss the very general member of the split Weil family.
- Proposition 5.16: the Abel–Prym curve of an étale cyclic triple cover deforms with its Prym variety only along the Prym locus, although its class stays algebraic on the whole split Weil family. When the curve is embedded and the Prym variety has maximal Hodge group, it is therefore not semiregular for n ≥ 4. This tests on a curve the question the paper leaves open for Schoen's subvariety, Question 5.14, and does not decide it.

The finite steps of both are checked in Python, Julia, C and Lean. The rest of the paper is unchanged from v1.0.1.
