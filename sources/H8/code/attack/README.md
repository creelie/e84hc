# The round-12 attack scripts

Round 12 ran four attack tracks against the inputs that the closure graph of
the paper leaves open. Each track was then checked by an adversarial verifier,
who reran the track's scripts, re-implemented its central computations
independently, and corrected its statements where they went too far. This
directory packages both, with the unedited transcripts of the runs. Every
statement below is the verifier's corrected one.

**Nothing here is a new unconditional case of the Hodge conjecture.** The
scripts establish exact numbers (dimensions, ranks, lattice indices,
Hochschild profiles) and the computational inputs of statements that are
reformulations of an open problem, exclusions, or implications whose
hypotheses remain open. Each claim carries its status: *proved* (a complete
argument; the scripts check it on cases), *computed* (an exact computation on
the stated cases), *conditional* (an implication whose hypothesis is open, or
which rests on a cited theorem that was not re-read), *sketch* (plausible, not
proved) or *open*.

| directory | track | subject |
| --- | --- | --- |
| `quartic_cm/` | T1 | the Weil classes `W_F` of a quartic CM field `F` at `n = 2` |
| `mumford_target/` | T2 | the first case of (F2): the square of a Mumford fourfold and the Kuga-Satake class of `S_lambda` |
| `explicit_objects/` | T3 | explicit objects on a split member `A = X x Xhat`, `K = Q(sqrt(-d))` |
| `natural_objects/` | T4 | natural objects on the split member at `n = 4` |

Each directory holds the track's scripts, the verifier's scripts in `verify/`,
and in `transcripts/` the logs of the runs that the reports and verdicts
quote, unedited (they are kept in git by a negation line in the repository's
`.gitignore`). `../attack_checks.py`, item (LV) of `verify_all.py`, runs a
fast subset; see the last section.

## Running

Every script runs as `python3 -B <script> [arguments]` from any working
directory: a script finds its helper modules in its own directory, and
`natural_objects/t4_n2_cross.py` finds the repository's `code/` two levels
above its own file. The flag `-B` (or `PYTHONDONTWRITEBYTECODE=1`) keeps
bytecode out of the tree. `quartic_cm/run_all.sh` and
`natural_objects/run_all.sh` rerun a whole track and its verifier and write the
new logs to `rerun/` (ignored by git), so that they can be compared with
`transcripts/`.

The runs used Python 3.11.15, python-flint 0.9.0, numpy 2.4.6 and sympy
1.14.0. Run times are wall-clock times of one run on one core of the packaging
machine, measured with four runs in parallel on four cores; where a transcript
records its own time, the two agree to within ten per cent.

All arithmetic is exact, over `Q`, `Q(i)`, `Q(sqrt(-d))`, a quartic CM field,
or the function field `Q(d)`, except where a rank is taken modulo a prime `p`.
A rank modulo `p` is at most the rank over the field, so a kernel computed
modulo `p` is an upper bound for the true kernel. Every such bound is used in
that direction only and is matched by an exact bound in the other direction.

What was changed in packaging; the scripts are otherwise as the tracks and
the verifiers ran them.

- `natural_objects/t4_contr.py` and `t4_example.py` put their own directory
  on `sys.path` instead of `'.'`. `natural_objects/t4_n2_cross.py` finds
  `code/` relative to its own file instead of by an absolute path, and takes
  the optional arguments `[box [d ...]]`; without arguments it runs as before,
  on the box of size 3 for `d = 1, 2`, and with another box its output lines
  name the box.
- The verifier's rerun of `t4_n2_cross.py` used a byte-identical copy, which
  is not kept separately; its log is `natural_objects/transcripts/rerun_n2_cross.log`.
- `quartic_cm/verify/v_binomial_9296.py` reconstructs the command, not saved
  by the verifier, that produced `quartic_cm/transcripts/v_binomial_9296.log`.
  Its output is identical to that transcript.
- The two `run_all.sh` scripts write to `rerun/` instead of next to the
  scripts or to `logs/`, and also run the verifier's scripts.
- Transcript names: the verifier's reruns of track scripts are prefixed
  `rerun_`; the `logs/` directories of track T4 and of its verifier were
  merged into `natural_objects/transcripts/`.

Every packaged script was rerun from its new place and exits normally, and
each one that has a transcript reproduces it apart from recorded times, with
one exception:
`explicit_objects/transcripts/v2_n2.log` was made by an earlier version of
`verify/v2_orlov.py`, which printed the Hochschild profile of the certificate
in degrees 0 to 4, `(1, 8, 18, 8, 1)`; the packaged version prints degrees 0 to
3, `(1, 8, 18, 8)`. The last entry is the first by Serre duality, and
`t3_verify.py` computes the whole profile. The transcripts
`t2_tensor_closure.log` and `t2_split_model.log` end with the output of `time`.

## `quartic_cm/`: track T1, `W(F,2,delta)` for a quartic CM field

`F = F_0(sqrt(-D))` is a quartic CM field with real quadratic `F_0`; `B` is an
abelian eightfold of `(F,2,delta)`-Weil type, with `H^1 = V = F^4` and a
hermitian form `H`; `W_F` is its 4-dimensional space of Weil classes. **Status:
`W(F,2,delta)` is open for every quartic `F` and every `delta`.** Nothing below
proves it.

1. *Computed.* At a member with Hodge group `Res_{F_0/Q} SU(V,H)`: `su(V,H)` has
   `Q`-dimension 30; `W_F` has `Q`-dimension 4 and is killed by `su(V,H)`; the
   Hodge classes in `H^2` have dimension exactly 2 (the `F_0`-twisted
   polarisations) and in `H^4` exactly 7 (3 products of divisor classes and 4
   Weil classes), and `W_F` meets the products in 0. Checked for `Q(zeta_5)`
   (cyclic), `Q(zeta_8)`, `Q(zeta_12)` (biquadratic) and `Q(sqrt(-(3+sqrt 2)))`
   (non-Galois, `D_4` closure), with `H = diag(1,1,-1,-1)`, `diag(1,1,-1,-3)`
   and `diag(1,2+s,-1,-(3+s))`: lower bounds by explicit exact invariants,
   upper bounds by kernels modulo `p = 1000003`.
2. *Proved.* `T = wedge^2_F H^1` (written `R_F` in the paper, Section `ssec:quartic`),
   inside `H^2(B,Q)`, has `Q`-dimension 24.
   Write `x ^_F y = q(x,y) Omega` and let `h` be the hermitian form induced by
   `H`. The `F`-semilinear `phi` with `q(x,y) = h(x, phi y)` satisfies
   `phi^2 = (det H)^{-1}` and commutes with `SU(V,H)`, but not with `U(V,H)`:
   `phi g = conj(det g) g phi`. So `phi` is a Hodge endomorphism of `T` on every
   member. At a Hodge-generic member, `End_Hdg(T) = F + F phi`, the cyclic
   algebra `(F/F_0, (det H)^{-1})`, which is split exactly when `delta` is
   trivial; the commutant of `su(V,H)` on `T` has `Q`-dimension 8.
3. *Proved.* `W_F(B)` is algebraic if and only if the Casimir class
   `C_q`, in `T (x) T` inside `H^4(B x B)`, is algebraic: `Delta^* C_q = 6 w(c)`,
   and `C_q` lies in the 20-dimensional `Q`-span of the pull-backs
   `f_{a,b}^* W_F`, `f_{a,b}(x,y) = ax + by`. So the Kuga-Satake, or
   exceptional-isogeny, route restates the problem and does not reduce it. The
   further equivalence with the algebraicity of `phi` is only a *sketch*.
4. *Proved.* `W_F(B)` lies in the subring generated by `NS(B)`, if and only if
   it meets that subring, if and only if `T` contains a nonzero rational Hodge
   class. The components of this Noether-Lefschetz locus `NL(T)` have
   dimension exactly 6 when `delta` is trivial and at most 4 otherwise, in a
   period domain of dimension 8. `W_F` is algebraic on `NL(T)`, by an explicit
   formula on the split locus `A (x)_{F_0} F`. The description of the
   components of dimension at most 4 (products of `(F,1)`-fourfolds, or an
   octic CM field acting) is a *sketch*.
5. *Proved, using Markman's theorem `W(K,2,delta)` as the paper cites it.*
   For biquadratic `F = K F_0` and `C` of `(K,2,delta)`-Weil type, `W_F(C (x)_{O_K} O_F)` lies in the
   10-dimensional `Q`-span of the pull-backs of `W_K(C)`, hence is algebraic, on
   a 4-dimensional locus. The locus is not contained in `NL(T)` (its generic
   point has no Hodge class in `T`), but it meets `NL(T)`, for example at
   `C = C_1 x C_2` with Weil surfaces `C_i`. It is not a new case: these are
   Hodge classes on `C x C`. That these loci are all the specialisations of
   `B` to products of two Weil fourfolds is a *sketch*.
6. *Proved, no script.* At a member with full Hodge group, if an abelian variety
   `Y` has no simple factor of dimension at least 8 on which a normal subgroup
   isogenous to `Hg(B)` acts, then `Hdg(B^a x Y^b) = Hdg(B^a) (x) Hdg(Y^b)`.
   *Conditional* on the theorems of Zarhin and of Looijenga-Lunts (recalled,
   not re-read): no Hodge structure of K3 type or of hyperkaehler type shares a
   Hodge class with `B` beyond products.
7. *Computed.* `dim HT^2(B) = 120 = 28 + 64 + 28`. A pure Weil class has
   `r = 80`, with annihilator `0 + 16 + 24`. A generic
   `gamma = N omega + p(theta_1, theta_2)`, and a general flat Hodge class with
   nonzero Weil part, have `r = 112`, the annihilator being the 8-dimensional
   tangent space of the polarised family. Monomial shapes give `r` in
   `{80, 84, 88, 104, 108, 112}`; binomial shapes give at least
   `{84, 88, 92, 96, 104, 108, 112}`, for example
   `r(omega + theta_1 + theta_0^2) = 92` and `r(omega + theta_0^2 + theta_1^2) = 96`
   (the two polarisations are `theta_0, theta_1` in `v_ann.py` and
   `theta_1, theta_2` in the track). *Proved:* `r(gamma) >= 68` for every `p`;
   the bound is not known to be sharp, and the least value found exactly is 80.
   So every perfect complex `E` with such a Chern character has
   `dim Ext^2(E,E) >= 68`. *Conditional:* if `dim Ext^2(E,E) = r(ch E)` at one
   point, then `sigma_E` is injective, and `W(F,2,delta)` follows given the
   `F`-version of the semiregularity closure theorem (thm:cmpropagation(v)).

| script | checks | run | time | transcript |
| --- | --- | --- | --- | --- |
| `t1lib.py` | quartic CM fields, exact linear algebra (a module) | | | |
| `t1_generic.py` | claim 1, six `(F, H)` pairs, 60 checks | `python3 -B t1_generic.py` | 44 s | `t1_generic.log` |
| `t1_T.py` | claims 2 and 3, four `(F, H)` pairs, 32 checks | `python3 -B t1_T.py` | 72 s | `t1_T.log` |
| `t1_loci.py` | claims 4 and 5: the split locus for three fields, the scalar-extension locus for four, 60 checks | `python3 -B t1_loci.py` | 42 s | `t1_loci.log` |
| `t1_annihilator.py` | claim 7: 120, 80 with `0 + 16 + 24`, 112 for six `gamma`, 104 for special shapes, 5 checks | `python3 -B t1_annihilator.py` | 5 s | `t1_annihilator.log` |
| `t1_lowerbound.py` | claim 7: the `p`-independent bound 68, 1 check | `python3 -B t1_lowerbound.py` | 0.2 s | `t1_lowerbound.log` |
| `t1_fullflat.py` | claim 7: `r = 112` for three general flat classes, 1 check | `python3 -B t1_fullflat.py` | 2 s | `t1_fullflat.log` |
| `t1_shapes_explore.py` | exploration: the 25 monomial shapes and a sample of binomials (the sample missed 92 and 96) | `python3 -B t1_shapes_explore.py` | 13 s | `t1_shapes_explore.log` |
| `run_all.sh` | all of the above and the verifier's scripts, into `rerun/` | `sh run_all.sh` | 5 min | |

The verifier re-implemented claim 7 in `verify/v_ann.py`: a separate model of
`HT^2` (bitmask exterior algebra, another order of generators, exact over `Q`
with python-flint), which gives 120; `r = 80` with `0 + 16 + 24` for four
coefficient vectors of `omega`; the explicit 8-dimensional tangent space, which
kills generic `gamma`, with `r = 112`; the monomial values; the `p`-support,
exactly the 256 products of the eight pairs; and the bound 68 for two
coefficient vectors (0.7 s, `v_ann.log`). Further: `verify/v_fullflat.py`, `r = 112` for
three general flat classes (0.3 s); `verify/v_binomial.py`, all 300 pairs of
monomials with seven ratios, which found 92 and 96 (33 s);
`verify/v_binomial_9296.py`, the 12 pairs of rank 92 or 96 (5 s);
`verify/v_minsearch.py`, exploratory, about 1800 exact evaluations, none below
80, not a proof of a minimum (66 s); and, for claim 2, `verify/v_phi.py`, which
checks `phi^2 = (det H)^{-1}` over `Q(zeta_5)` in `F`-coordinates with a
non-diagonal `H` and an element `g` of `U(V,H)` with `det g` not in `Q` (2 s). The
counts 2 and 7 of claim 1 were re-derived by representation theory, and
claims 2 to 6 by hand. The verifier's reruns of the six check scripts, 159
checks with none failed, are `transcripts/rerun_*.log`. Each script in `verify/`
runs as `python3 -B verify/<script>` and has the transcript of the same name.

## `mumford_target/`: track T2, the first case of (F2)

`X` is a very general member of a Mumford family (setup:mumford), with Hodge
group `G`, over `Qbar` a quotient of `SL_2^3` acting on
`V = V_1 (x) V_2 (x) V_3 = H^1(X)`; `F` is the totally real cubic field,
`T = Lie G`, and `S_lambda` is the K3 surface of Picard number 13 with
`T(S_lambda) = T(-1)` (thm:mumfordks). **Status: the first case of (F2), the
algebraicity of the two exceptional classes of `X x X`, is open, and so is the
algebraicity of the Kuga-Satake class of `S_lambda`.**

1. *Computed.* `KS(S_lambda)` is isogenous to `X^32` and to `B^4` with
   `B ~ X^8` and `End^0(B) = M_8(Q)`; after the isogeny the Kuga-Satake class is
   a `32 x 32` matrix of elements of the `F`-line
   `Hom_Hdg(T(S), H^1(X)^{(x)2}(1)) = F`. `T` occurs in no `H^k(X)(j)`. The
   `F`-dimension of `Hom_Hdg(T, H^n(X x X)(j))` is 1, 6, 16, 24, 16, 6, 1 for
   `n = 2, 4, ..., 14`, and 0 otherwise; the copy in `H^2` lies in
   `H^1 (x) H^1` and has Hodge numbers `(1,7,1)`.
2. *Proved.* The Kuga-Satake class has a nonzero component in
   `T(S) (x) H^*(A)`, `A` an abelian variety, and products of pull-backs of
   algebraic classes from the two factors have none, so no such product gives
   it; a new correspondence between `S_lambda` and an abelian variety is needed.
3. *Proved, a conditional theorem.* If the two exceptional classes of `X x X`
   are algebraic, then every Hodge class on every `X^n` is algebraic, and
   `B(W^{(n)})` holds for every fibre power. The step that needs a computation:
   the `S_4`-span `T4_0` of the degree-4 Hodge classes of `X x X`, in the
   `(1,1,1,1)` Kuenneth component of `H^4(X^4)`, has dimension 7 and misses the
   class `Det` spanning `det(Q^4) (x) Sym^4(V)^G`, on which `S_4` acts by the
   sign (`Det(x,x,x,x)` is 6 times Cayley's hyperdeterminant); one composite of
   two correspondences in `T4_0` has nonzero `Det` component, and the composites
   fill all 8 dimensions of `(V^{(x)4})^G`. Schur-Weyl for `SL_2^3` does the
   rest: `s_k = Cas_k + 1/2`, `dim End_G(V (x) V) = 8`, the partial swaps
   generate the 125-dimensional `End_G(V^{(x)3})`, and `(V^{(x)6})^G` has
   dimension 125. Consequently (b) of cor:mumfordequiv is equivalent to the
   Hodge conjecture for all `X_t^n` at every non-CM point `t`. At the CM points
   the Hodge conjecture for all `X_c^n` holds unconditionally, by Markman's
   theorem for abelian fourfolds and the zero-sum property: the minimal
   zero-sum multisets of the weights `{+-1}^3` have no repeated weight. The
   Tannakian check in the report is a *sketch* and is not needed. Novelty was
   not established.
4. *Conditional on the algebraicity of the Kuga-Satake class* (no script). The
   Hodge conjecture holds for `S_lambda^a x X^b` for all `a, b`.
5. *Proved* (no script). The Kuga-Satake class of `S_lambda` is algebraic if
   and only if the two exceptional classes are algebraic and some algebraic
   cycle on `S_lambda x X^n` acts nontrivially on `T(S_lambda)`. So the
   Kuga-Satake route is at least as strong as the first case of (F2); whether
   the first condition implies the second is unknown.
6. *Proved.* An abelian variety `Y` with `T(S_lambda)` a subquotient of
   `H^k(Y)(j)` has `dim Y >= 6`. The bound is attained Hodge-theoretically by
   the unitary Hodge structures of weight one with `H^1 = D`, `End = K` a CM
   quadratic extension of `F` inside `D`, where `T` has Hodge numbers `(1,7,1)` in
   `H^2`; that abelian sixfolds realise them (Shimura's unitary curves) was
   recalled, not re-read. So no algebraic cycle acting nontrivially on
   `T(S_lambda)`, as in claim 5, can factor through an abelian variety of
   dimension at most 5.
7. *Proved* (no script). For a smooth complete intersection surface `Sigma` in
   `X`, the first case of (F2) is equivalent to the Hodge conjecture for the
   real-multiplication classes on `Sigma x Sigma`.
8. *Proved* (no script). At a CM point `c` of the Mumford curve, `S_c` has
   Picard number 16 and a transcendental lattice of rank 6 with CM by a sextic
   field.

| script | checks | run | time | transcript |
| --- | --- | --- | --- | --- |
| `t2_weights.py` | claims 1 and 6: highest-weight peeling for `SL_2^3`, the multiplicities, the unitary model; 7 checks | `python3 -B t2_weights.py` | 0.1 s | `t2_weights.log` |
| `t2_tensor_closure.py` | claim 3 in the non-crossing-matching model: `dim (V^{(x)4})^G = 8`, `T4_0` of dimension 7 without `Det` (exact), a contraction with nonzero `Det` component (exact), fullness in degrees 4 and 6 (ranks modulo `p`, lower bounds); 12 checks | `python3 -B t2_tensor_closure.py` | 205 s | `t2_tensor_closure.log` |
| `t2_split_model.py` | claim 3, the split model over `Q`: the Casimir identity, the partial swaps, `dim End_G(V (x) V) = 8`, the stabiliser of dimension 9, the 125-dimensional algebra; 16 checks | `python3 -B t2_split_model.py` | 440 s | `t2_split_model.log` |

The verifier re-implemented claims 1, 3 and 6. `verify/v1_weights.py` uses the
Weyl alternating-sum formula instead of highest-weight peeling and recomputes
the multiplicities, the copy of `T` in `H^1 (x) H^1` with Hodge numbers
`(1,7,1)`, and the unitary model (0.1 s, 11 checks). `verify/v2_pullbacks.py`
is an independent implementation of the load-bearing step of claim 3, exact
throughout, in the exterior algebras `wedge^*(V (x) Q^m)` with Koszul signs: the
degree-4 Hodge classes of `X x X` (dimensions 1, 1, 4, 1, 1), `(V^{(x)4})^G` of
dimension 8, pull-backs along 45 integer matrices and products of pulled-back
divisors spanning 7 dimensions, `Det` outside that span, and composites
reaching all 8 (13 s, 10 checks). `verify/v4_schurweyl.py` checks the facts
used in Schur-Weyl: the Casimir identity, the images 2, 5, 14 of the group
algebras, the Catalan number 5, and the discriminant 49 (0.6 s, 7 checks).
`verify/v3_cm_hilbert.py` computes the irreducible zero-sum multisets of the
weights `{+-1}^3` with multiplicities at most 5, which are the four pairs
`{w, -w}` and two quadruples (5 s, 4 checks). The verifier's reruns of
`t2_weights.py` and `t2_tensor_closure.py` are `transcripts/rerun_*.log`.
Claims 2, 4, 5, 7 and 8 have no script and were checked by hand.

## `explicit_objects/`: track T3, explicit objects at a split member

`A = X x Xhat` with the `K`-action of eq:Mdef, `K = Q(sqrt(-d))`, `X` principally
polarised with classes `beta, betahat, ell` and `eta = d beta + betahat`; `T` is
the tangent space of the polarised Weil family at `A`; `Phi` is Orlov's
equivalence `D(X x X) = D(X x Xhat)`; `P_theta` is the secant plane.
**Status: no new case. The certificates below are for cases already known
(Markman: all Weil fourfolds, and sixfolds of trivial discriminant), and
turning them into algebraicity needs a twisted semiregularity theorem (the
paper cites Perry for the twisted Buchweitz-Flenner theorem) together with the
extraction of untwisted cycles.**

1. *Computed.* The graph-type abelian subvarieties `Z_{p:q}` have
   `[Z] = D^n/n!`, `D = q^2 beta - pq ell + p^2 betahat`; their classes span a
   space of dimension `2n + 1` that contains the Weil plane and not `eta^n`.
   With `omega_1 = Re (gamma - sqrt(-d) ell)^n` (the normalisation of
   thm:splitclosed(iii), minus the `omega_1` of ex:splitsmall at `n = 2`),
   `omega_1 = 4[0 x Xhat] + 4[X x 0] - [Z_{1:1}] - [Z_{1:-1}]` at `n = 2`, `d = 1`.
   The least `N` with `N omega_1` in the lattice of subvariety classes depends
   on the normalisation. `Ext^2 = 60` and `rank sigma = 18` refer to the
   particular shifted and translated sum of `zsigma.py`.
2. *Proved (summand principle).* If `sigma_E` is injective and
   `v _| ch(E) = 0` for all `v` in `T`, then every direct summand `F` of `E` has
   `v _| ch(F) = 0`, so `ch(F)` lies in `Q[eta] + HW`. The `T`-flat rational
   classes are computed to be exactly `Q[eta] + HW` at `n = 2` and at `n = 3`,
   `d = 1`.
3. *Proved (single-summand form).* If `sigma_E` is injective and `ch(E)` is
   `T`-flat, no direct summand of `E` has as Chern character a rational multiple
   of a pure spinor outside `Q[eta]`: line bundles, semi-homogeneous bundles or
   sheaves on abelian subvarieties with slope off `Q eta`, structure sheaves
   of abelian subvarieties, points, and their Fourier-Mukai images.
4. *Proved.* For a nonzero secant class `v` on `X`, the rank of
   `HT^k(X) -> H^*(X)`, `xi -> xi _| v`, is `(1, 2n, 2C(n,2), ..., 2C(n,n-1), 1)`
   for `k = 0..n`, and 0 beyond; `chi(F,F) = 2^{n-1} (-1)^{n/2} d^{n/2-1}
   (a^2 d + b^2)` for `n` even and 0 for `n` odd, when `ch(F) = a u_t + b v_t`.
   Hence `dim Ext^k(F,F) >= 2C(n,k)` for `k = 1, 2`.
5. *Computed, over `Q(d)`.* For `E = Phi(F_1 [x] F_2^vee)` with secant `F_i`,
   `kappa_B = ch(E) e^{ell/2}` lies in `Q[eta] + HW`, its moments satisfy
   `mu_{m+2} = -mu_m/(4d)` (Hankel rank 2), and for `F_1 = F_2` with
   `ch = a u_t + b v_t` its Weil part is
   `((a^2 - b^2/d) omega_1 + 2ab omega_2)/(2 n!)`: identities over `Q(d)` for
   `n <= 5`. `ch(E)` itself is flat only after `e^B` with `B = +-ell/2` modulo
   `Q eta`, on every principally polarised `X`; the sign depends on the
   convention for Orlov's equivalence (eight conventions checked). The
   comparison with Markman's `kappa(E)` makes sense only when `rk E != 0`.
6. *Proved (twisted certificates).* At `n = 2`, for every `d`, with
   `F = O_C(p)` on a genus-2 Jacobian (and `F = I_p` at `d = 1`),
   `E = Phi(F [x] F^vee)` has `Ext^*(E,E) = (1,8,18,8,1)`, the Hochschild profile
   of `ch(E)`, so `dim Ext^2 = 18 = r(ch E)` and `sigma_E` is injective; that
   `r(ch E) = 18` for every `d` follows from the Kuenneth count
   `r(ch G) = 16 + 1 + 1`. At `n = 3`, for `d = k(k+1)`, with
   `F = i_* O_{C^(2)}((2k+1)x - k theta)` on the theta divisor of a genus-3
   Jacobian, `Ext^*(E,E) = (1,12,48,74,48,12,1)` and
   `dim Ext^2 = 48 = r(ch E)`. At `n = 2`, `R = 3/4` with `c_1 = c_3 = 0`, and the
   first-order Hodge locus of `kappa_B` among all tori has dimension 5; at
   `n = 3` it has dimension 9.
7. *Proved (with the verifier's hypothesis).* At `n = 4`, for perfect complexes
   `F_1, F_2` with secant Chern characters and `Ext^{<0}(F_i,F_i) = 0` (sheaves,
   for example), `dim Ext^2(E,E) > 88 = r(ch E)`: equality would force the
   profile `(1,8,12,8,1)`, with `chi = -2`, while a secant `chi` is at least 8.
   The argument does not apply to complexes with nonzero `Ext^{<= -3}`.
8. *Computed.* At `n = 2`, `S^2(E[1]) (x) P` (`c_1(P) = ell`) is untwisted and
   flat, of rank 3, with Weil part `omega_1/d`, `R = 3/4` after an `eta`-twist,
   and `r = 23`, which is odd; by the parity of prop:p2primeprofile(iii),
   `dim Ext^2 = r` is impossible. `Lambda^2(E[1]) (x) P` has rank 1, no Weil
   part, and `r = 12`. At `n = 3` both have rank 0 and `r = 57`.
9. *Conditional.* Suppose that for a fixed `d` and unboundedly many `n` a
   principally polarised abelian `n`-fold carries `F` with `ch(F)` in `P_theta`,
   nonzero, `Ext^{<0}(F,F) = 0` and `dim Ext^{0,1,2}(F,F) = (1, 2n, n(n-1))`. Then
   `sigma_E` is injective for `E = Phi(F [x] F^vee)`, and with a twisted
   semiregularity closure prop:descent gives `W(Q(sqrt(-d)),n,delta)` for all `n`
   and `delta`. The existence of such `F` is *open*. For this template the
   untwisted criterion fails; that is not a proof that (P2') itself must be
   twisted.
10. *Erratum, found by the verifier.* ex:splitsmall printed, at `n = 3`,
    `omega_1 = gamma ell^2 - gamma^3/3`, which lies in the Weil plane only for
    `d = 1`; the correct class is `d gamma ell^2 - gamma^3/3`. The paper has
    been corrected, and item (X) now checks the displayed formulas.

| script | checks | run | time | transcript |
| --- | --- | --- | --- | --- |
| `ext.py`, `split.py`, `orlov.py` | exterior algebra, the split member, Orlov's transform (modules) | | | |
| `t3_verify.py` | all claims in eight sections, 56 checks | `python3 -B t3_verify.py` | 22 s | `t3_verify.log` |
| `subvar.py` | claim 1: the classes `[Z_{p:q}]`, the tangent space `T` | `python3 -B subvar.py` | 2 s | |
| `zsums.py`, `zsmall.py`, `zsigma.py` | claim 1: integer combinations of `[Z_{p:q}]`, the sum used for `Ext^2 = 60` | `python3 -B <script>` | 0.5 s, 24 s, 0.1 s | |
| `tflat.py` | claim 2: `T`-flat rational classes `(1,1,3,1,1)` at `n = 2` | `python3 -B tflat.py` | 0.6 s | |
| `xrank.py`, `n4.py` | claim 4: profiles and `chi(F,F)`, `n = 2..6` | `python3 -B <script>` | 0.9 s, 0.3 s | |
| `bilinear.py`, `bilinear4.py` | claim 5 at the listed `d`, `n = 2, 3, 4` | `python3 -B <script>` | 1 s, 3 s | `bilinear.log`, `bilinear4.log` |
| `scan_n2.py`, `scan_n3.py`, `scan_n3b.py`, `t_basic.py`, `t_orlov.py`, `t_orlov2.py`, `t_orlov3.py` | exploration behind claims 5 and 6 | `python3 -B <script>` | at most 3 s each | |
| `n3cert.py`, `locus.py` | claim 6: the `n = 3` certificate, the first-order loci and `R` | `python3 -B <script>` | 3 s, 0.7 s | |
| `n4A.py` | claim 7: flatness and `r(ch E) = 88` at `n = 4` | `python3 -B n4A.py` | 12 s | `n4A.log` |
| `sym2.py`, `sym2b.py` | claim 8 | `python3 -B <script>` | 0.3 s, 0.1 s | |

The verifier wrote an independent exterior algebra (`verify/ea.py`, with sorted
tuples instead of bitmasks), a model of the split member in which the Weil
classes come from the eigenspaces of the `K`-action (`verify/model.py`), and
Orlov's transform (`verify/orl.py`, and `verify/orl_fast.py`, validated against
it). With them: `v1_basic.py`, the model, `T`, the Weil classes (1.5 s, no
transcript); `v4_subvar.py`, claim 1 with 24 slopes (2 s); `v7_tflat.py`, the
`T`-flat classes of claim 2 at `d = 1, 2, 5` and at `n = 3` (15 s);
`v8_xprofile.py`, claim 4 at `d = 1, 7, 10`, values the track did not use
(2 s); `v2_orlov.py`, claims 5 and 6, run as `python3 -B verify/v2_orlov.py 2
1,2,3,5,6,7,11 prof` (1 s, `v2_n2.log`) and `python3 -B verify/v2_orlov.py 3
1,2,3,5,6 prof` (10 s, `v2_n3.log`); `v3_symbolic.py` (`n = 2, 3`, 2 s) and
`v3b_symbolic.py` (run as `python3 -B verify/v3b_symbolic.py 4,5`, 53 s),
claim 5 with `d` a symbol; `v11_n4.py`, flatness at `n = 4` for `d = 1, 7, 21`
(2 s); `v12_conventions.py`, the eight conventions for Orlov's equivalence
(2 s); `v9_rG.py`, the Kuenneth count `r(ch G) = 18, 48, 88` at new values of `d`
(3 s); `v10_locus.py`, the first-order loci 5 and 9 (0.6 s); `v6_sym2.py`,
claim 8 at `d = 1, 2, 3, 7` (0.7 s); `v5_exsplit.py`, the erratum of claim 10
(0.1 s, no transcript). Claims 2, 3, 7 and 9 were re-derived by hand; the
hypothesis `Ext^{<0} = 0` in claims 7 and 9 is the verifier's correction.

## `natural_objects/`: track T4, natural objects at `n = 4`

`A = X x Xhat` at `n = 4`, `K` imaginary quadratic; the natural objects are line
bundles, twisted structure sheaves `O_B (x) L` of abelian subvarieties, simple
semi-homogeneous bundles, points, and their images under autoequivalences;
`H_A` is the Hodge ring at a very general `X`; `B_(p,q) = {(p x, q phi x)}`.
**Status: no new case. `W(K,4,delta_0)` stays open; closing the remaining gap
(one indecomposable perfect complex) would give `W(K,4,delta_0)`, and
`W(K,3,delta)` by descent, but not the Hodge conjecture, whose remaining (P2)
input concerns CM fields of degree at least 4.**

1. *Proved, for `K` imaginary quadratic (summand lemma).* If `E` is a direct
   sum `(+) F_i[k_i]` with a corrected character and `sigma_E` is injective on
   `ev_E(T)`, then every `ch(F_i)` lies in `(+) Q theta^k + HW`; if `N != 0`, some
   `F_i` has Chern character `omega' + sum c_k' theta^k` with `omega'` a nonzero
   rational Weil class (not necessarily a multiple of `omega_1`) and
   `dim Ext^2(F_i,F_i) >= 2n(2n-1)`; and if `sigma_E` is injective, so is
   `sigma_{F_i}`. This reduces (P2') to indecomposable objects; it does not
   do so for the flatness form of prop:p2flat.
2. *Proved, for `K` imaginary quadratic.* No direct sum of objects with
   `dim Ext^2 < 2n(2n-1)`, in particular of natural objects, has a corrected
   character with `N != 0` and `sigma_E` injective on `ev_E(T)`; so it fails (P2') and the weakened criterion, and
   has `dim Ext^2 > r(gamma)`.
3. *Computed.* `H_A` has dimensions 14, 30, 55 for `n = 2, 3, 4`, by degree
   1, 3, 6, 10, 15, 10, 6, 3, 1 at `n = 4`; it is `H^0(Q^3, O(n))^dual` with
   `Q^3 = LG(2,4)`, and `ch(F) = Phi_n(P(L_F)^n)` for a rational Lagrangian `L_F`.
   `W_1, W_2 = 24 (Re, Im/delta) P(1,-delta)`; `Q[theta]` is spanned by the
   conic `C_theta`, whose plane is the polar plane of the line `l_W` through
   `L_+` and `L_-`. For Fourier-Mukai images this rests on the standard
   description of autoequivalences through the spin representation (recalled).
4. *Proved for `X` very general, given the model of 3 (minimal support).* A
   combination of natural Chern characters plus `Q[theta]` equal to
   `N omega + sum c_k theta^k`, `N != 0`, uses at least 8 distinct Lagrangians off `C_theta`; with exactly 8
   they lie on one smooth conic through `l_W` and the combination is a pure
   Weil class. At `n = 2, 3` the same gives at least `2n`. Natural direct sums
   at `n = 4` have `dim Ext^2 >= 224 > 104`.
5. *Computed.* The lattice of subtorus classes has rank 9 and index
   `2612736000 = 2^12 3^6 5^3 7` (Smith invariants 1, 1, 1, 2, 6, 6, 120, 120,
   2520; a property of binary octics, independent of `d`); it meets the Weil
   plane in `Z(3/2 W_1) + Z(7/2 W_2)` (`d = 1`), `Z(5/6 W_1) + Z(35/6 W_2)`
   (`d = 2`), `Z(5/4 W_1) + Z(5/4 W_2)` (`d = 3`). The eight subtori with
   `(p,q) = (1,+-3), (1,+-2), (2,+-1), (3,+-1)` and
   `m = (-1, 16, -16, 1, -16, 16, 1, -1)` give `sum m_i [B_i] = 14 W_2` in the
   convention `phi^* = -B^{-1}`, and `-14 W_2` in the convention
   `phi^* = +B^{-1}`; over all 12870 eight-sets with `|p|, |q| <= 3` this is the
   least relation (`sum m^2 = 1028`, `sum |m| = 68`).
6. *Computed.* The explicit sum
   `E = (+) O_{B_i}^{|m_i|}[k_i] (+) O(eta) (+) O(2 eta) (+) O(3 eta)`, `d = 1`, has
   Hankel rank 3, `r = 104`, `dim Ext^2 = 28868`, `dim Ext^1 = 8248`, and
   `6 <= kappa <= 28` (the lower bound exact over `Q(i)`); the flatness form of
   prop:p2flat fails for it.
7. *Computed.* At the split member, `dim T = 16`, `T` kills `eta, W_1, W_2`,
   and `rank(T -> H^*, v -> v _| ch F) = 6` for every natural `F` off `C_theta`
   (`Ann_T(ch F)` is the 10-dimensional tangent space of the split locus), 0 for
   `O(eta)` and the point; exact over `Q(i)`. `r(gamma) = 56, 72, 88, 104` for
   `rho = 0, 1, 2, 3` (the values of thm:p2primenumber), and
   `rank(HT^2 _| ch F) = 28` for natural `F` (modulo `p`, a lower bound; 28 is
   also `dim Ext^2(F,F)`).
8. *Proved, corrected.* If the cross-`Ext^1` graph of a direct sum of natural
   objects is acyclic and the relevant `Ext^2` groups vanish, the flatness form
   of prop:p2flat fails. This covers every direct sum, with any shifts and
   multiplicities, of `O_{B_i} (x) L_i` for pairwise distinct `n`-dimensional
   abelian subvarieties meeting pairwise in finite sets (cross `Ext` in degree
   `n`, arrows raising the shift by `n - 1`).
9. *Computed.* The paper's exhaustive `n = 2` search (item (XIII)) on the box
   of size 3 finds 888 (`d = 1`) and 30 (`d = 2`) signed tuples with flat
   character and nonzero Weil part, all of four terms with all four Lagrangians
   off `C_theta`; 192 and 18 of them lie on a conic through `l_W`, and these
   are exactly the ones with a pure Weil character (the script counts both; the
   identification tuple by tuple is the verifier's argument). On the box of
   size 2, the run of `attack_checks.py`, the numbers are 184 and 20 tuples, of
   which 56 and 12 lie on such a conic, and as many are pure.

| script | checks | run | time | transcript |
| --- | --- | --- | --- | --- |
| `ext.py`, `lg.py`, `contraction.py`, `tspace.py` | exterior algebra, the Lagrangian Grassmannian model, contraction and `T` modulo `p` (modules) | | | |
| `t4_basic.py` | claim 3: `H_A`, the Weil classes, the subtorus classes | `python3 -B t4_basic.py d`, `d = 1, 2, 3` | 0.2 s | `basic_d1.log`, ... |
| `t4_lg.py` | claim 3: the Veronese model at `n = 4` | `python3 -B t4_lg.py d`, `d = 1, 2, 3` | 10 s | `lg_d1.log`, ... |
| `t4_lg_n.py` | claim 3 for `n = 2, 3, 4` | `python3 -B t4_lg_n.py n d` | 0.1 s, 2 s, 34 s for `n = 2, 3, 4` | `lg_n2_d1.log`, ... |
| `t4_minimal.py` | claim 4 on examples | `python3 -B t4_minimal.py d`, `d = 1, 2` | 27 s | `minimal_d1.log`, `minimal_d2.log` |
| `t4_sublattice.py` | claim 5: index and intersection with the Weil plane | `python3 -B t4_sublattice.py d H` (`1 10`, `2 8`, `3 8`) | 0.1 s | `sublattice_d1.log`, ... |
| `t4_subtori_search.py` | claim 5: the least relation | `python3 -B t4_subtori_search.py 1 3` | 1 s | `subtori_search_d1.log` |
| `t4_weil_lattice.py`, `t4_unit_search.py` | exploration behind claim 5 | `python3 -B <script>` | 5 s, 0.1 s | |
| `t4_example.py` | claim 6 | `python3 -B t4_example.py d [small]` (`1 small`, `1`, `2`) | 9 s | `example_d1_small.log`, `example_d1_ref.log`, `example_d2_ref.log` |
| `t4_contr.py` | claim 7, modulo `p` | `python3 -B t4_contr.py d`, `d = 1, 2` | 7 s | `contr_d1.log`, `contr_d2.log` |
| `t4_n2_cross.py` | claim 9 | `python3 -B t4_n2_cross.py [box [d ...]]` | 226 s (box 3), 31 s (box 2) | `n2_cross.log` |
| `run_all.sh` | all of the above and the verifier's scripts, into `rerun/` | `sh run_all.sh` | 8 min | |

The verifier wrote an independent exterior algebra (`verify/v4lib.py`, which
imports nothing from the track) and with it: `v1_relations.py d`, claims 3
to 5, the dimensions of `H_A`, the Weil classes from the eigenspaces, the
relation `14 W_2` in both conventions, and the configurations of the minimal
support proof on three conics through `l_W` (5 s for each `d = 1, 2, 3`,
`v1_d1.log`, ...); `v2_lattice.py`, the Smith normal form with sympy after a
python-flint Hermite normal form, for the boxes 6, 8, 10 (0.3 s);
`v3_tspace.py d`, claim 7 exactly over `Q(i)`, without reduction modulo `p`
(14 s for each `d = 1, 2`, `v3_d1.log`, `v3_d2.log`); `v4_search.py`, the
exhaustive search of claim 5 through the closed form of the `m_i`, checked
against exact kernels (1 s); `v5_chi.py`, the intersection numbers of claim 6
(0.2 s). Claim 9 was reproduced by rerunning `t4_n2_cross.py`
(`rerun_n2_cross.log`), not re-implemented; claims 1, 2, 4 and 8 were re-derived
by hand, with the corrections recorded above (the scope `K` imaginary
quadratic, `omega'` in place of `omega_1`, and the dimensions `n`, `n - 1` of
claim 8).

## What `attack_checks.py` runs

`../attack_checks.py` (item (LV)) runs, each in a subprocess with `python3 -B`,
the following, reads the numbers they print and turns them into 48 checks, in
about two and a half minutes on one core.

- `quartic_cm/`: `t1_generic.py` on two of its six pairs (`Q(zeta_5)` with
  `diag(1,1,-1,-3)` and `Q(sqrt(-(3+sqrt 2)))` with `diag(1,2+s,-1,-(3+s))`,
  14 s) and `t1_T.py` on one (`Q(zeta_5)`, `diag(1,1,-1,-3)`, 18 s), through a
  short driver that calls their own functions; `verify/v_phi.py`,
  `t1_annihilator.py`, `verify/v_ann.py`, `t1_lowerbound.py`, `t1_fullflat.py`,
  `verify/v_fullflat.py`, `verify/v_binomial_9296.py`. These check the counts
  2 and 7, `phi^2 = (det H)^{-1}`, the commutant 8, the Casimir span 20, the
  numbers 120, 80 (`0 + 16 + 24`), 112 and the bound 68, and the values 92 and
  96.
- `mumford_target/`: `t2_weights.py`, `verify/v1_weights.py`,
  `verify/v2_pullbacks.py`, `verify/v4_schurweyl.py`,
  `verify/v3_cm_hilbert.py`. These check the multiplicities of `T`, the
  7-of-8 span and the composite reaching `Det`, the Schur-Weyl numbers, and the
  zero-sum property at the CM points.
- `explicit_objects/`: `t3_verify.py`, `verify/v8_xprofile.py`,
  `verify/v2_orlov.py 2 1,2,3,5,6,7,11 prof`, `verify/v9_rG.py`,
  `verify/v3_symbolic.py`, `verify/v10_locus.py`, `verify/v6_sym2.py`,
  `verify/v5_exsplit.py`. These check the Hochschild profiles, the `n = 2` and
  `n = 3` certificate numbers, the count 88 at `n = 4`, the parity numbers of
  `S^2(E[1]) (x) P`, and the erratum of ex:splitsmall.
- `natural_objects/`: `verify/v3_tspace.py 1`, `t4_contr.py 1`,
  `verify/v1_relations.py 1`, `verify/v2_lattice.py`,
  `t4_sublattice.py 1 10`, `verify/v4_search.py`, `verify/v5_chi.py`, and
  `t4_n2_cross.py 2`. These check `dim T = 16` and the rank 6, the values of
  `r(gamma)`, the relation `14 W_2`, the lattice index, the least relation, and
  the `n = 2` cross-check on the box of size 2.

The long runs (`t1_generic.py` and `t1_T.py` in full, `t1_loci.py`,
`t2_tensor_closure.py`, `t2_split_model.py`, `t4_lg_n.py 4 d`, `t4_minimal.py`,
`t4_n2_cross.py` on the box of size 3, `verify/v3b_symbolic.py 4,5`) are not
repeated; their transcripts are here.

## gaps/: the three remaining inputs, attacked through their smallest cases

A later attack, with the computations re-run and wired into item (LV) as its
part (E). Nothing here is a new case of the Hodge conjecture for abelian
varieties; each directory holds the programs and their transcripts.

| directory | subject | status |
| --- | --- | --- |
| `quartic_obstruction/` | the propagation statement for a quartic CM field at n = 2: the secant space S(t,q) of a quartic field and its Hochschild profile (Proposition prop:quarticsecant); the integral classes of the F_0-Hodge ring (Lemma lem:quarticlattice): the local expansion with delta and the entries of V as symbols (`a1_lattice_local.py`), and the saturation computed directly for d_F = 5, 8, 13, 17, 40 in the product model S (x) M (`a1_lattice.py`, `a1_Lgen.py`) and for d_F = 12, 24, 28, 40, 56 on the lattice O^2 + (d^-1)^2 (`a1_lattice_general.py`); the arithmetic of prop:quarticother for every real quadratic field (`a1_rank2_arith.py`: N(x + 4y) = N(x) mod 4 with D a symbol, the parity at the prime above 2, and the conditions on m for squarefree D < 200000, which leave only D = 2 and D = 5); flatness of the twisted character of an Orlov product for F0 = Q(sqrt D), D = 2, 3, 5, 7, 10, 13, 17 (`a1_flat.py`, `a1_flat_general.py`), the formula r(kappa) = r^2(v_1) + 64 + r^2(v_2) on eight pairs, with the values 100, 102, 104 and, for F = Q(sqrt 5, i) and a class of N_w = 2, 88 and 94 (`a1_rkappa.py`, `a1_rkappa_general.py`), and the identities of the proof on random integral classes; an exact scan of 1841 planes for Q(sqrt 10) (`a1_general.py sqrt10 2 12`); together these give thm:quarticobstruction, no dimension-count certificate from Orlov products for any quartic CM field | proved; the finite arithmetic is also certified in Lean (Sections 32 and 34) |
| `sextic/` | the dimension count beyond degree four: the Hochschild profiles of the secant classes of a sextic CM field (`s1_profile.py`, exact over Z at two random points): palindromic, r^1 = 12, r^2 = sum rho_j + 4 sum N_jk, generic profile (1, 12, 54, 112, 54, 12, 1); chi = (-4)^3 N(q) sum |w|^2 < 0; a minimal object needs only -chi >= r^3 - 2 r^2 + 22 (values -6 to 26), so no class is excluded after scaling; an independent check of Proposition prop:sexticcount, whose own program is `code/sextic_count.py`, item (LVI); the quartic profile is reproduced as a regression test | computed; the thresholds are also certified in Lean (Section 35) |
| `orlov_growth/` | the Orlov template in every dimension: flatness of the twisted character for all n (prop:flatall, checked at n = 1, 2 with d a symbol; all n by tensor factorisation) and the equality criterion with negative Ext groups (prop:orlovequality); sheaves on divisors (prop:divisortemplate: room for n >= 5 with Ext^<0 = 0, no line bundle on a smooth divisor for n >= 4, the Ext groups of i_*(V\|_Theta), and no bundle restricted from X at n = 5; `divisor_sheaves.py`, exact, with b and d symbols) | proved; the counts of prop:orlovequality are certified in Lean (Section 33) |
| `f3prime/` | (F3') implies (M), and the closure graph with that rule added (prop:f3primestrength); the powers of a variety of orthogonal type, where the first open class is det(V) on Y^t (prop:orthpowers) | proved |

Run each program with `python3 -B <program>` from its directory;
`../attack_checks.py` runs them all as part (E) of item (LV).
