# Review of Hongmin Li's related Fermat-fourfold preprints

This review concerns **On the Hodge conjecture for Fermat varieties**, in
`creelie/e84hc`. It is separate from **Algebraic Hodge Loci and Exceptional
Correspondences** in `creelie/fermat-hodge-`.

## Publication and statement overlap

DataCite identifies Hongmin Li as the author of **The Hodge Conjecture for
Odd-Degree Fermat Fourfolds**, DOI 10.13140/RG.2.2.26853.77288. The record was
created and registered on 8 September 2026 at 15:31:45 UTC. Its source has
the date 7 September, and the inspected GitHub snapshot is commit
8131ed824db6ca99c3698d19b9972e9f13da723c of
Li-Hongmin/hodge-odd-fermat-fourfolds. Theorem 1.1 states the rational
Hodge conjecture for every odd-degree Fermat fourfold.

The first record in the author's e84hc Zenodo series was created on
8 October 2026 (10.5281/zenodo.23234363, then carrying an earlier title).
Theorem B's all-odd-degree assertion is present in release v1.2.0,
published on 10 October. Thus the September preprint is an earlier
statement-level precedent for Theorem B. This chronological conclusion
does not depend on accepting either infinite proof as correct.

Li's later **Residual Characters of Odd-Degree Fermat Fourfolds** is
archived at 10.5281/zenodo.24054303. The archive identifies its manuscript
as rStation paper 104, v4, publicly posted 5 November 2026. Zenodo's own
record was created 8 November; the revision distinguishes the manuscript
date from the archive-creation date. This later work cites Bhattacharjee's
profile descent and credits Jumagulov for the seed constructions.

## What was checked

The comparison examined the statements, the positive predicates, the
six seed constructions, the final classification assembly in Theorem
7.20 and its listed dependencies. The accompanying independently written
standard-library check verifies every unit translate of seven named
tuples, their inverse-pair and surface-contraction predicates, exact
5-standard membership, every admissible move for these inputs, the
displayed identities and profiles, and inflation at 3m and 5m.

At degree 21, the terminal tuple admits a positive surface contraction.
The second degree-39 residual admits a profile-lowering move. The residual
at 45 and both residuals at 105 admit direct moves. The degree-33 and
first degree-39 residuals are shared terminal representatives. Hence the
lists of three terminal and six residual orbits do not contradict one
another. Appendix C includes the details and an elementary proof that
inflation preserves and reflects the positive predicates.

These checks do not enumerate every sextuple, do not prove a uniform
conductor classification, and do not construct arbitrary algebraic
cycles by computation. No local Lean build was performed. The September
repository itself distinguishes its finite Lean endpoints from its
infinite and Chow-theoretic arguments.

## What is not independently certified by this review

This is not a complete verification of Li's September conductor descent
or November Theorem 7.20. Such a verification would have to check the
exact-order Fourier relations, lower-order contributions, the short-kernel
classification (including parity and small-prime cases), the zero-row
case and every step reducing arbitrary prime support to the six seeds.
It would also have to check the external geometric correspondences and
their nonvanishing hypotheses. Agreement of finite tests is not a
substitute for those arguments. No conclusion that these proofs are
wrong follows from the present limited audit.

The cited preprints are therefore used for accurate attribution and
comparison, not as new proof inputs. The existing proof of Theorem B
retains its own classification, profile-descent and exceptional-cycle
lemmas. The all-dimensional degree-57 route through a class at level 114
is a different assertion from the algebraicity of X^4_57. Conversely the
degree-33 and degree-39 fourfold classes were already in Jumagulov's
finite-degree work; known consequences through Aoki's reduction should
not be advertised as exclusive new discoveries.

## Changes made

- Added both verified Li references, including visible DOI links.
- Acknowledged the September statement of Theorem B and the earlier
  diagonal-class counterexample to Kang's tensor identity.
- Removed the assertion that the all-odd-degree conclusion is new beyond
  degree 199 and qualified overlapping all-dimensional consequences.
- Corrected the introduction's list of exceptional Aoki divisors to
  include 33 and 39 alongside 57, 44, 52 and 51.
- Added Appendix C, a comparison diagram and finite arithmetic checks.
- Preserved the title, sole author, all original theorem labels and the
  complete earlier manuscript. No correspondence was sent to Li.

The general Hodge conjecture and the manuscript's universal F2 and F3'
inputs remain unproved.
