**When is every rational Hodge class algebraic?**
Deep Bhattacharjee. Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India.
d.bhattacharjee@erl-forschung.de · itsdeep@live.com · ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X)

The paper determines which combinations of the standard statements around the rational Hodge conjecture imply it. Every such combination contains the conjecture modulo abelian varieties, unless it contains both the Lefschetz standard conjecture and André's conjecture that every Hodge class is motivated, a pair equivalent to the Hodge conjecture itself.

Granting the recently claimed Hodge conjecture for CM abelian varieties, it proves the conjecture for every Fermat variety and reduces the abelian case to propagation from CM points. For Weil classes it proves a criterion by bounded degree at CM points. It also extracts from Schoen's cycles one subvariety whose semiregularity would settle the split Weil families over Q(√−3) in every dimension.

**The Hodge conjecture itself is not proved.** Section 7 of the paper lists what is proved, what is proved under a stated hypothesis, and what remains open.

### Files

- `when-is-every-rational-hodge-class-algebraic.pdf`: the paper, 29 pages, `amsart`.
- `when-is-every-rational-hodge-class-algebraic-tex.zip`: the full LaTeX source, with the figures as PNG and their TikZ sources.
- `when-is-every-rational-hodge-class-algebraic-arxiv.tar.gz`: the arXiv submission, containing `main.tex`, `sections/`, `main.bbl` and the PNG figures. It compiles with pdflatex alone.

The workflow attaches these files to the release once the paper has been built on GitHub.

### Checks

`verification/shell/run_all.sh` re-runs the finite steps:

- `closure_checks` in Python, Julia and C, in exact arithmetic, with identical 196-line outputs;
- a Lean 4 file that uses the core library only, with no `sorry` and no `native_decide`;
- Macaulay2 scripts for the Jacobian-ring Hodge numbers and Max Noether's theorem.

All 61 references were checked online. No proof in the paper depends on a computer.

### Citation and DOI

Zenodo assigns a DOI to this release when the repository is switched on in the author's Zenodo GitHub settings. The metadata is in `.zenodo.json` and `CITATION.cff`.
