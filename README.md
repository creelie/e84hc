# On the Hodge conjecture for Fermat varieties

**Deep Bhattacharjee**

Current research revision: [v1.9.0](https://github.com/creelie/e84hc/releases/tag/v1.9.0). Version DOI: awaiting confirmation of this new release archive.

Permanent work DOI, printed in the manuscript: https://doi.org/10.5281/zenodo.23234362

## Current manuscript

- [PDF](papers/fermat.pdf): 86 pages, amsart.
- [Complete TeX ZIP](papers/fermattex.zip): main.tex, bibliography, figures and ancillary checks.
- [Revision notes](papers/next-version-submission-notes.md).
- [Related-work review](papers/related-work-review.md).
- [Reference verification](papers/bibliography-additions-audit.md).
- [AI provenance](papers/aiprovenance.md).

## Results and scope

Theorem A concerns Fermat varieties in every dimension for degrees 2^a 3^b 11^c, 2^a 3^b 13^c, and 2^a 3^b 17^c or 2^a 3^b 19^c with a at most one, together with their products and Fermat-type abelian varieties. Its coniveau argument uses uniruled character quotients and does not use Kang's product estimate.

Theorem B gives a profile-descent proof of the rational Hodge conjecture for odd-degree Fermat fourfolds. The same conclusion was stated earlier by Hongmin Li in his September preprint, [DOI 10.13140/RG.2.2.26853.77288](https://doi.org/10.13140/RG.2.2.26853.77288). His later [residual-character paper](https://doi.org/10.5281/zenodo.24054303) uses different positive predicates. The explicit seed constructions are credited to Rifat Jumagulov.

Adds two verified references to Hongmin Li, acknowledges his September precedent for Theorem B and the diagonal-class counterexample, distinguishes the later six-residual classification from the three-terminal profile descent, and adds Appendix C with an inflation lemma, a comparison diagram and exact checks of seven named tuples. The whole earlier paper is retained, with its title and sole author unchanged. Claims of exclusive priority for the overlapping odd-degree conclusion are removed. The review does not independently certify Li's infinite conductor arguments.

The universal Hodge conjecture and the general F2 and F3-prime inputs remain unproved. Li's papers are cited as preprints for attribution and comparison; they are not new proof inputs. No fresh full Lean build or formalization of the whole paper is claimed.

## Build and check

Compile paper/main.tex with pdfLaTeX, run BibTeX, then rerun pdfLaTeX until references settle. Run python paper/anc/check-li-comparison.py for the new finite checks. The existing verification code retains its stated scope. The active papers folder contains one current PDF and one current source ZIP. Earlier versions remain in release history; independent source material and proof certificates are preserved.
