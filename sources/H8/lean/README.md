# Machine verification for *Algebraic Loci of Weil Classes on Abelian Varieties*

`HodgeObstruction.lean` is a certificate, checked by the Lean 4 kernel, of the
finite arithmetic on which the results of the paper turn.

## What this does and does not claim

The theorems of the paper are statements of algebraic geometry and are **not**
formalised. The cohomology of an abelian variety, the Hodge decomposition, the
Fourier-Mukai transform, Grothendieck-Riemann-Roch, the Lefschetz hyperplane
theorem, hard Lefschetz and the invariant theory of `SL_{2n}` are used as
mathematics and none of them is formalised here. What is formalised is the
finite arithmetic listed in the table below; the computations of the paper
that are not, and why, are listed after it.

## Running it

A Lean 4 toolchain and nothing else. No Mathlib, no dependencies.

    elan toolchain install $(cat lean-toolchain)
    lake build
    lean HodgeObstruction.lean

`lake build` builds the package declared in `lakefile.toml`; the second line
prints the axiom report. Each takes about one hundred minutes and about 7 GB of memory. Silence from the elaborator means the kernel
accepted every theorem; the block at the foot of the file then prints one line
per theorem. Every line must read `does not depend on any axioms`, or
`depends on axioms: [propext]` where propositional extensionality enters
through `decide` or the core lemmas on natural numbers, and none may mention `sorryAx`. The GitHub workflow in
`.github/workflows/lean.yml` enforces all three, and fails the build if the
number of theorems is not four hundred and nine or if any of them reaches for a further
axiom.

## The four hundred and nine theorems

| theorem | statement |
| --- | --- |
| `qnorm_mul_check` | the norm on `Z[sqrt(-d)]` is multiplicative on the data used |
| `qmul_conj` | `tau * conj(tau)` equals the norm |
| `characters_differ` | `tau^(2n) != N(tau)^n` at `tau = 2 + sqrt(-d)`, nine fields, `n <= 8` |
| `characters_differ'` | the same at five further witnesses |
| `bad_witness` | the witness `tau = 1 + sqrt(-d)` fails at `(d,n) = (1,4)` and `(3,3)` |
| `bad_witness_exceptions` | and fails exactly when `d=1, 4|n` or `d=3, 3|n` |
| `ratio_not_root_of_unity` | `tau^n != conj(tau)^n` at `tau = 2 + sqrt(-d)` |
| `sign_uniform_and_closed` | the Fourier-Mukai sign is uniform over index sets and equals `(-1)^(g(g+1)/2+k)`, `g <= 5` |
| `subsets_count` | the subset enumeration used there has `C(g,k)` members |
| `semiregularity_target` | `sum_q C(2n,q) C(2n,q+2) = C(4n,2n-2)`, `n <= 7` |
| `secant_count_below_thresholds` | `2n^2+2n < 2^(2n) < 3^(2n)`, `2 <= n <= 8` |
| `thresholds_not_necessary` | `3 < 2^2` and `5 < 3^2`, the two retracted claims |
| `grading_positions_differ` | `(2n,0)`, `(0,2n)` and `(n,n)` are distinct cells for `n >= 1` |
| `weil_delta_parity` | `sqrt(-d)^k` is rational exactly when `k` is even, `k <= 20` |
| `weil_delta_closed_even` | `sqrt(-d)^(2m) = (-d)^m` |
| `weil_delta_closed_odd` | `sqrt(-d)^(2m+1) = (-d)^m sqrt(-d)` |
| `weil_term_counts` | each generator of the Weil line has `2^(2n-1)` monomials |
| `supports_disjoint` | a monomial of the Weil line is never a monomial of a power of `eta` |
| `hodge_dim_count` | `dim Hdg^k = 3` for `k = n` and `1` otherwise, `n <= 6` |
| `weil_line_hodge_type` | the Weil line is of type `(n,n)` exactly when the signature is balanced |
| `clifford_dimensions` | `dim C = 2^b`, `dim C^+ = 2^(b-1)`, `dim KS = 2^(b-2)` |
| `k3_type_only_at_one` | `h^(2,0) = 1` on the pieces of `H^2` forces `n = 1` |
| `moduli_codimension` | the Weil family has codimension `n(n+1)` in `A_{2n}` |
| `discriminant_is_a_norm` | `d^n p^2` is a norm from `K`, with an explicit witness |
| `split_codimension` | the split locus has codimension `n(n-1)/2`, zero only at `n=1` |
| `quat_class_odd` | for `n` odd the quaternionic discriminant class is `b` times a square |
| `quat_class_even` | for `n` even it is a square |
| `quat_product_class` | `d^(n-1)` is a norm for `n` even, with an explicit witness |
| `quat_locus_codimension` | the quaternionic locus has dimension `n(n+1)/2` and codimension `n(n-1)/2` |
| `quat_locus_divisor_at_two` | at `n = 2` that locus is a divisor: `4`, `3`, `1` |
| `irrational_witness_exists` | some `m <= 7` makes `(m + sqrt(-d))^(2n)` irrational, `n <= 8` |
| `weil_line_spanned` | the determinant of `w, tau*w` is `b(w1^2 + d w2^2)`, hence nonzero |
| `norm_form_positive` | `a^2 + d b^2 > 0` for every nonzero `(a,b)`, ten fields |
| `norm_sum_forces_zero` | a positive combination of norms vanishes only when every term does |
| `semiregularity_source_target` | the source overtakes the target at `s = 5` when `n = 2` |
| `secant_witness_at_n_four` | the line bundle witness of the theorem on secant sheaves reproduces `6 (u + v)` in every degree at `n = 4`, `d = 3` |
| `secant_witness_rank` | that witness has rank `6`, which is `M a` and is positive |
| `vandermonde_nodes_distinct` | the Vandermonde product on the nodes `0, ..., n` is nonzero for `n <= 8` |
| `level_sums_forced` | the level sums recorded in the theorem on semiregular split objects satisfy `sum_j M_j N_j^r = 0` for `r = 1,2,3`, at six level sets |
| `level_sums_totals` | their totals are `1`, `3` and `-2`, so none of the objects has rank zero |
| `level_matrix_nonsingular` | with at most `n` distinct norms the matrix `(N_j^r)` is nonsingular, so every level sum vanishes |
| `gauss_norm_counts` | the number of Gaussian integers of norm `1, 2, 3, 4, 5, 9, 45` |
| `norm_supply_blocks_small_case` | at the nodes `1,2,3,4` the forced `|M_3| = 4` while `Z[i]` has no element of norm `3` |
| `pencil_volume` | `int eta^4 = 4! (2d)^4 = 384 d^4` on `O^2`, as a polynomial identity in `d` |
| `pencil_square` | `C_k^2 = (1 + k^2) I` for the matrix of the pencil, so `phi_k^2 = (1 + k^2)/(4 d^2)` |
| `pencil_minimum` | `(8/24) beta(k) int eta^4 = 32 d^2 (1 + k^2)`, the minimum `mu_k` |
| `pencil_degree_bound` | `mu_k int eta^4 / 2 = 6144 d^6 (1 + k^2)` and `6144 = 32^2 6`, the degree bound |
| `split_obstruction_rank` | `n^2 - n(n+1)/2 = n(n-1)/2` and `n(n-1) = 2 (n(n-1)/2)` for `n <= 30`: the rank of the obstruction map of a split object and the even side of the semiregularity kernel |
| `split_obstruction_count` | the bookkeeping of the explicit object at `n = 3`: kernel `15 = 9 + 6`, tangent copy `9`, obstruction image `3`, direct sum `12`, complement `3` |
| `evaluation_not_surjective` | `s C(2n,2) > 2 C(2n,2) + 4n^2` for `5 <= s <= 40` and `2 <= n <= 30`, so the evaluation map of a sum of five or more line bundles is not surjective; at `n = 3`, `s = 6` the dimensions are `66` and `90` |
| `markman_candidate_identities` | for odd `d <= 201` and `N = (d+9)/2`: `12N(N-5) = (d+9)(3d-3)`, at least `(d+9)(2d-1)`; `110N - 12N^2 + 2N(2d-1) = (d+9)(27-d)`; `9 - 2N = -d` and `81 + 36N - (d+9)(27-d) = d^2`, the secant point `(1,3)`; `N(3 + sqrt(-d)) = 2N`; the ranks `8d(d+9)` and `8d(d-9)` are nonzero for `d` not `9` |
| `secant_kernel_arithmetic` | the matrix `[[a, b], [b, -ad]]` cutting out the classes that preserve `a u_t + b v_t` has determinant `-(a^2 d + b^2)`, nonzero for `(a,b)` not `(0,0)`, `a, b < 13`, `d <= 20`; the coefficients `C_k = k! c_k` satisfy `C_(k+1) = -d C_(k-1)`, which makes the Poisson compensation uniform in the degree; and `n(n+1)/2 + n(n-1)/2 = n^2` for `n < 60` |
| `candidate_unnormalised_points` | for odd `d <= 201`: `(d+9)(3d-3) - (d+9)(2d-1) = (d+9)(d-2) >= 12`, so Markman's candidate always has an unnormalised double point; normalising every isolated point gives `chi = 50 N`, never the secant value `72 N - 4 N^2` |
| `tensor_rank_gap` | `C(2n,2) >= 6 > 1` for `n >= 2`, the tensor rank separation |
| `smooth_invariants` | Noether and the self-intersection formula for a smooth support: `K^2 + e = 12 chi` and `K^2 - e = 6(b^2+d)^2` |
| `smooth_bmy_defect` | the Bogomolov-Miyaoka-Yau defect of a smooth support is `24(b^4 - d^2)` |
| `smooth_bmy_is_d_le_bsq` | so the inequality is exactly `d <= b^2`, over a box in `b` and `d` |
| `smooth_index_vacuous` | the Hodge index bound `9(b^2+d) >= 8b^2` holds for every `d >= 1`, so it never binds |
| `smooth_four_discriminants` | the squarefree odd `d <= 9` are exactly `1, 3, 5, 7` |
| `smooth_table` | the invariants at `b = 3` and those four `d`, as printed in the paper |
| `burch_weight_identities` | the weight `x^2+d` annihilates three moments of the difference, `c_{k+2} + d c_k = 0` |
| `burch_rank_one_discriminant` | nine times the discriminant of the rank one quadratic is `-2b^2 - 18d`, always negative |
| `burch_rank_four_witness` | the rank four candidate at `d = 23` solves the moment system and is removed only by injectivity |
| `closure_omits_conjecture` | the Hodge conjecture is not in the forward closure of what the paper proves and quotes |
| `frontier_suffices` | it is in the closure once (F3) alone is adjoined, the conjecture for the varieties that are not abelian, which covers A x P^1 and so is the conjecture itself; once {Lefschetz standard conjecture, every Hodge class motivated} is adjoined; once (F3'), the conjecture modulo abelian varieties, is adjoined with the Lefschetz standard conjecture, with the variational statement for algebraic classes, or with (P2) for the split families of the CM fields of degree at least four and (F2); and, not minimally, once that (P2), (F2), (F3) or {Lefschetz standard conjecture, (F3)} or {variational statement, (F3)} is |
| `frontier_minimal` | in each of the five minimal sets, {(F3)}, {Lefschetz, motivated}, {Lefschetz, (F3')}, {variational, (F3')} and {(P2) for the split families of the fields of degree at least four, (F2), (F3')}, every element is necessary: dropping any one leaves the conjecture underivable |
| `frontier_smallest` | of the sixteen open statements exactly one, (F3), suffices alone, and of the one hundred and twenty pairs exactly those containing (F3) and the pairs {Lefschetz, motivated}, {Lefschetz, (F3')} and {variational, (F3')} suffice |
| `variational_gives_abelian` | the variational statement for algebraic classes alone puts the conjecture for abelian varieties in the closure, and not the conjecture |
| `lefschetz_gives_abelian` | the Lefschetz standard conjecture gives the variational statement, hence the conjecture for abelian varieties, and not the conjecture |
| `secant_route_descends` | granting both open demands of the secant route reaches the trivial discriminant and, by descent, every imaginary quadratic family, and neither the CM fields of higher degree nor the conjecture |
| `propagation_closes` | the propagation statement for the split imaginary quadratic families puts the whole imaginary quadratic case in the closure, and for the split families of the fields of degree at least four it puts the Weil classes of every CM field there |
| `p2_minimal_count` | `binom(4n,2) - 4n^2 = 2 binom(2n,2) = 2n(2n-1)` for every `n <= 60`: the dimension at which the semiregularity criterion is met automatically |
| `mumford_invariants` | the invariants of `sl_2^3` in `wedge^q (V_1 (x) V_2 (x) V_3)` have dimensions `1, 0, 1, 0, 1, 0, 1, 0, 1`, counted from weight multiplicities: the monodromy invariants of a Mumford family are the powers of the polarisation, which the theorem on the Lefschetz operator of an abelian scheme over a curve needs |
| `two_branch_annihilator` | for n = 2, 3 the monomials of type (p,p) killed by `Q HH^1`, `P HH^1` and `HH^1 HH^1` are `alpha_-`, `alpha_+` and none: the annihilators behind the theorem that an object meeting the semiregularity criterion is not a direct sum of objects with exterior Ext algebras |
| `mumford_rigidity_sos` | a positive multiple of each of the seventeen forms P1, P2, Q1..Q4, R, S1..S4, Z1..Z6 is a sum of squares of integral linear forms with positive coefficients, checked on `{0,1,2}^4`, which suffices for polynomials of degree at most two in each variable: the certificates behind the rigidity of the exceptional classes of a Mumford square |
| `mumford_ext_profile` | the lower bounds `1, 16, 119, 328, 560, 328, 119, 16, 1` for the self-extensions of an object with the Chern character of an exceptional class are palindromic, have alternating sum 112 and sum 1488, and give 800 in even degrees against a Hochschild bound of 688 in odd degrees, so chi(E,E) = 0 forces Ext^1 + Ext^3 >= 400 |
| `lefschetz_counts` | the Sp_8-invariants of wedge^*(V+V) number `1, 3, 6, 10, 15, 10, 6, 3, 1` by the decomposition of each wedge^i V into fundamental modules, the Hodge classes of the Mumford square that are not Lefschetz number `0, 0, 2, 6, 13, 6, 2, 0, 0` (twenty-nine), the Lefschetz classes at a CM point are counted by the coefficients `1, 16, 100, 304, 454, ...` of `(1 + 4y + y^2)^4`, and Weyl's formula for Sp_8 gives `27, 42, 308` for `varpi_2, varpi_4, 2 varpi_2`, with `1 + 27 + 42 + 308 = 378` |
| `criterion_endomorphisms_n2` | for all natural numbers, `2 e0 + 12 = chi + 2 e1` with `e1 >= 8` and `chi >= 1` gives `e0 >= 3`: an object meeting the numerical criterion at n = 2 has at least three endomorphisms |
| `criterion_endomorphisms_n3` | for all natural numbers, `2 e0 + 60 = chi + 2 e1 + e3` with `e1 >= 12`, `e3 >= 40` and `chi >= 1` gives `e0 >= 3`: the same at n = 3 |
| `weil_monomials_separated` | neither Weil monomial lies in the exterior algebra on `V_-^{1,0} + V_+^{0,1}` or on `V_+^{1,0} + V_-^{0,1}`, for `n <= 12`: the Weil line misses every class pulled back from a quotient by an abelian subvariety tangent to an eigenspace |
| `quartic_squares_mod4_phi` | the squares modulo `4` in `Z[phi]`, `phi^2 = phi + 1`, are `0, 1, 1 + phi, 2 + 3 phi` |
| `quartic_no_square_phi` | neither `-1` nor twice a unit is a square modulo `4` in `Z[phi]`: the case `Q(sqrt 5)` of the rank-two argument |
| `quartic_squares_mod4_sqrt2` | the squares modulo `4` in `Z[sqrt 2]` are `0, 1, 2, 3 + 2 sqrt 2` |
| `quartic_no_square_sqrt2` | `3`, `1 + 3 sqrt 2` and `1 + sqrt 2` are not squares modulo `4` in `Z[sqrt 2]` |
| `quartic_rank_two_congruences` | `m = 9` has no solution `1 <= m <= 8` modulo `13` or `17`, and modulo `5` only `m = 4` |
| `quartic_euler_minimal` | the minimal profiles `1, 8, r, 8, 1` with `r = 18, 20, 12` have Euler characteristic `4, 6, -2` |
| `orlov_equality_count` | `n(n-1) + (2n)^2 + n(n-1) = 6n^2 - 2n` for `3 <= n <= 64`, and `1 + 16 + 1 = 18` |
| `orlov_n4_euler` | the minimal profile at `n = 4` has `chi = -2`, while every secant character has `chi = 8d(a^2 d + b^2) >= 8` (for all natural numbers) |
| `quartic_squares_mod4_mod8` | a square is `0` or `1` modulo `4`, an odd square `1` modulo `8`, twice a square `0` or `2` modulo `8` |
| `quartic_rank_two_small_odd_parts` | the rank-two conditions on `m` in `[1, 8]` for `D = 3, 7` and `D = 6, 10, 14` have no solution, and for `D = 2` leave `m = 1, 5` |
| `quartic_rank_two_large_odd_part` | for every modulus `n >= 10` no `m < 9` is `9` modulo `n` (for all natural numbers) |
| `quartic_sqrt2_units_mod4` | `3` and `1 + 2 sqrt 2` are not squares modulo `4` in `Z[sqrt 2]`, `(1 + sqrt 2)^2 = 3 + 2 sqrt 2`, `(3 + 2 sqrt 2)^2 = 1` modulo `4`, and `5` is not `+-1` modulo `8` |
| `sextic_thresholds` | the thresholds `r^3 - 2 r^2 + 22` of the six computed sextic secant profiles are `2, -6, 10, 26, 8, 12`, the generic minimal Euler characteristic is `-26`, and `(-4)^3 = -64` |
| `cm_tetrahedra` | the zero-sum four-sets of the eight weights `(+-1, +-1, +-1)` are six unions of opposite pairs and the two tetrahedra `T_+`, `T_- = -T_+`, each meeting every opposite pair once |
| `cm_square_monomials` | on the square, `132 = 100 + 32` monomials of weight zero, the `32` being tetrahedron monomials distributed `1, 4, 6, 4, 1` on each tetrahedron |
| `cm_tetrahedron_pairs` | the six two-element subsets of `T_+` fall into three pairs by the set of coordinates in which their weights differ |
| `cm_profile_forces_equal` | on the box `[-10, 10]^3`, equal values of `abs(a_2 - a_3)`, `abs(a_1 - a_3)`, `abs(a_1 - a_2)` force `a_1 = a_2 = a_3` |
| `cm_pairs_three_cycle` | a permutation of the four diagonals of the cube fixing none of the three pairings is a three-cycle |
| `cm_abelian_semiregular_count` | for `1 <= n <= 60`, the annihilator of the class of an abelian `n`-fold in an abelian `2n`-fold has dimension `6n^2 - n`, and its complement in `HT^2` has dimension `C(2n, 2)` |
| `quartic_rank_values` | the tuples `(mu, rho_1, rho_2, R_1, R_2)` allowed at a quartic CM field give exactly fifteen values of `64 + 16 mu + 4 rho_1 + 4 rho_2 + R_1 + R_2`, the least `80` only at `(0, 0, 0, 8, 8)`, never `100`, and nine values when `rho_1 = rho_2` |
| `delsarte_loop_sextic` | for the loop sextic, `A B = 15624 I` with `B` the circulant `(3125, -625, 125, -25, 5, -1)`, rows of `B` summing to `2604`, and Jacobian ring dimensions `1, 426, 1751, 426, 1`, total `15625` |
| `simplex_klein_quartic` | for the Klein quartic, `C R = 7 I` with `R` the exponent matrix in the chart `z = 1` and `C` explicit, `det R = 7`, `det A = 28` for the full exponent matrix, and `C` not zero modulo `7`, so the lattice exponent is `7`; the Euler number summed over the torus strata is `-4`, the value `((1 - 4)^3 - 1 + 12) / 4` of a smooth plane quartic |
| `simplex_loop_sextic` | for the loop sextic, `C R = 2604 I` with `C` explicit, `det R = 2604 = 2^2 * 3 * 7 * 31`, and `C` not zero modulo any of these primes, so the lattice exponent is `2604`; the Euler number summed over the torus strata is `2610` for the loop and for the Fermat sextic, the value `((1 - 6)^6 - 1 + 36) / 6` of a smooth sextic fourfold |
| `quartic_exceptional_pair` | in the exterior algebra of `V_s + V_s'` at a real place of a quartic CM field, `theta^4 = 24 alpha_s alpha_s'` and `(alpha_s + alpha_s')^2 = 2 alpha_s alpha_s'`; `theta^3 D = 0` and the `theta^2 D` are four distinct monomials for `D` in `V_s^{0,1} (x) V_s'^{0,1}`; and the two deformations `xi'_0`, `xi''_0` that are not `F`-linear send `alpha_s`, `theta`, `theta^2` to `theta b_{s,0} b_{s,1}`, `2 b_{s',0} b_{s',1}`, `4 theta b_{s',0} b_{s',1}` and symmetrically, so the place is exceptional exactly when `16 c^2 = u_s u_s'` |
| `quartic_locus_counts` | the rational characters with both places exceptional have rank `94` or `110`; the annihilator of a character has dimension `8 + 4a + b`, one of `8, 9, 10, 12, 13, 16`; `so(4,3)` has dimension `21` and maximal compact subalgebra of dimension `9`, `su(2,2)` has `15` and `7`, and the orbits have dimension `21 - 16 = 5` and `15 - 11 = 4` |
| `quartic_compensated_bivectors` | in the exterior algebra on `H^1(X) = U_1 + U_2`, with `q = 2`, the classes `x_j = (pi_j _| theta_j^2, 0, pi_j)` annihilate the four classes spanning `S(0,2)`, and the six symmetric maps at the two places annihilate `theta_1` and `theta_2` (`decide +kernel`) |
| `quartic_rank_certificates` | a `20 x 20` minor of the contraction matrix of `4 beta'` and a `12 x 12` minor of that of `alpha_0`, for `f_1 = 2`, `f_2 = 1/2`, are invertible modulo `1000003` (`decide +kernel`) |
| `quartic_koszul_squares` | for the Koszul resolution of `R/(x_1,...,x_c)`, `c = 3, 4`, the Yoneda square `a_k a_l` is represented by a nonzero vector exactly when `k != l` and `k, l <= c`, and the coboundaries vanish at the origin |
| `quartic_line_two_planes` | a nonzero vector of `[-6,6]^4` has a nonzero component outside one of two complementary coordinate planes |
| `quartic_first_factor_character` | the pieces of Markman's Example 8.2.4 have the characters used there, `ch(F_d) = Theta - (d/6) Theta^3` and `chi(F_d, F_d) = 8 d` for `d <= 60` |
| `conv_pure_weil_identity` | for `n = 2, 3, 4` there are `2 * 4^(n-1)` exponent vectors `zeta` in `mu_4^n` with `prod zeta = +-1`, half of each sign, and the signed sum of the `e^(c_1(L_zeta))` has coefficient `2 * 4^(n-1)` on `alpha` and on `conj(alpha)` and `0` on every other monomial in the `c_j`, `c'_j` (`decide +kernel`) |
| `conv_cup_kernel` | at `n = 3` the graphs `Gamma_tau` of the six types of diagonal classes have `4` components when `tau` has an entry `2` and `16` otherwise, so the classes constant on components span `3 * 4 * 1 + 3 * 16 * 4 = 204` dimensions, `249` with the `45` classes of the multiples, out of `525` (`decide +kernel`) |
| `conv_run_excess` | for `3 <= n <= 12` and every placement of `p` among the `t_i`, a run from a piece `L_zeta` through distinct multiples back has excess at least `2n - 4 >= 2`, and a closed walk through the multiples alone at least `2n - 3`; at `n = 2` a run of excess `0` exists (`decide +kernel`) |
| `conv_esix_thresholds` | along `M_2 -> M_3 -> L -> M_1` with `Ext` degrees `0, 6, 0` the shifts are `d, d + 1, d - 4, d - 3`, the product lands in `Ext` degree `6` and `sigma_1 = sigma_3 = -sigma_2`; `r = 24, 57, 104` at `n = 2, 3, 4`; `(t_2 - t_1)^6 = 1, 64, 729`, `249 - 64 = 185 > 57`, `249 - 57 = 192`, and `(t_2 - t_1)^6 >= 192` exactly when `t_2 - t_1 >= 3` |
| `ff_partner_counts` | with `zeta_j = i^(e_j)`, the sixteen pieces with `prod zeta = 1` and the sixteen with `prod zeta = -1`; every piece has `3`, `6`, `7` partners of the other parity differing in `1`, `2`, `3` coordinates, and for the `7` the block dimension `D = prod_j |zeta_j - zeta'_j|^2` is `16` six times and `64` once, `160` in all; the `112` pairs carry `2560` classes (`decide +kernel`) |
| `ff_shift_table` | in the three placements of the multiples relative to `p`, the shifts `mu_i`, `nu_i` of a piece one step from or to `M_i` and the extremes `lambda_i`, `kappa_i` over steps between the multiples are those of the table in the proof of the lemma on pieces that differ everywhere, and satisfy `lambda_i <= 0 <= kappa_k`, `kappa_i >= lambda_i + 2`, `lambda_i <= mu_i + 2`, `nu_i <= kappa_i + 2` (`decide +kernel`) |
| `ff_noconvolution_counts` | the kernels `11`, `19` of `x_1`, `x_3` on a surface at `t = (2, 5, 6)`; the cover degrees; `3^6 = 729`, `16 * 24^3 = 221184`, `4^6 = 4096`; and the bounds `249 - (45 + 15 * 9) = 69 > 57` and `16 * 12 = 192 > 57` of the theorem that no convolution of the pieces meets the criterion. The rank `192` of the fourfold products is certified in ball arithmetic by part (H) of item (LXXII), not here |
| `efour_partner_counts` | at `n = 4`, the `128` pieces of `(Z/4)^4` of even sum, `64` of each parity; each has `4, 12, 28, 20` partners of the other parity differing in `1, 2, 3, 4` coordinates, those differing in one coordinate differ there by `2`; the `28` have `D = 16` twenty-four times and `64` four times, `640` in all; `64 * 640 = 40960 > 104 = 7 * 16 - 2 * 4` |
| `efour_run_drop` | with `p` at any rank among the four values, every run from `p` through two selections of distinct multiples back to `p`, the marked step between them a component or a class of `H^1(a, a)`, changes the shift by at most `-4`, a step up by `+1` and a step down by `-7`: the finite core of the lemma on shifts along chains at `n = 4` |
| `efour_two_level_degrees` | with `p` at any rank, every pair of chains `c -> ... -> W`, `V -> ... -> e` through distinct multiples, not both empty, gives `Ext` degree `4 - U + 7D` different from `3` when `c = e`, from `0` when `e` is above `c` and from `8` when `e` is below `c`: the case analysis of the two-shift theorem on `E_0^8` |
| `vandermonde_counts` | the genus of the generalised Fermat curve by Riemann-Hurwitz equals that by adjunction for `d = 2..7`, `N = 2..8`; `r! d^(N(r-1)) = 16, 32, 54, 1536, 162` at the five cases of the fibre count; the units of `Z/d` number `1, 2, 2, 2` for `d = 2, 3, 4, 6`; the balanced characters with six nonzero coordinates and a fixed zero number `20, 140, 1750`, so `70, 490, 6125` orbits in `P^6` and at least `141, 981, 12251` Hodge classes |
| `vg_chain_determinants` | the intersection matrix of a chain of `m` vanishing cycles (`1` above the diagonal, `-1` below) has determinant `1` for `m` even and `0` for `m` odd, `m = 1..7`, so `2g` cycles of the chain form a basis of `H_1` of a hyperelliptic curve of genus `g` |
| `vg_quadric_counts` | `1 + sum_{j > r/2} C(N+1, 2j)` equals one plus the number of subsets of `{0..N}` of even size at least `r + 2`, for `N <= 9`, `r = 2, 4, 6`; it is `N + 2` for two quadrics in `P^N`, `N` even, `2` for a quadric of even dimension, and `2, 8, 30, 94, 257` for `r = 4`, `N = 5..9` |
| `vg_cubic_counts` | `1 + C(N+1, r+2) C(r+2, r/2+1)` equals one plus the number of vectors in `{0,1,2}^(N+1)` with `r + 2` nonzero entries, `r/2 + 1` of them equal to `1`, and sum divisible by `3`, for `N <= 7`, `r = 2, 4`; it is `7, 21, 71` for the Fermat cubics of dimension `2, 4, 6`, `141` for two cubics in `P^6` and `631` for two cubics in `P^8` |
| `vg_triple_signatures` | for `n_1, n_2 < 20` branch points of exponents `1, 2` with `n_1 + 2 n_2` divisible by `3`, the signature `p = (2 n_1 + n_2)/3 - 1`, `q = (n_1 + 2 n_2)/3 - 1` gives back `n_1 = 2p - q + 1`, `n_2 = 2q - p + 1`, the branch data of Achter and Pries, and `p = q` exactly when `n_1 = n_2` |
| `cyclic_base_count` | the vectors of nonzero residues modulo `m = 3, 4, 6` with `5` or `6` coordinates, sum `0`, order `m` and `p, q >= 1`, written as count vectors, number `38` up to sign: the cases with five or six branch points of the proposition on the monodromy of cyclic covers, which the paper proves by hand |
| `cyclic_merge_small` | every such vector with `7 <= k <= 8, 11, 10` coordinates at `m = 3, 4, 6` has two entries `u, w` with `u + w != 0` whose merge keeps the order `m` and `p, q >= 1`: a check of the merge lemma, which the paper proves by hand |
| `cyclic_norms` | `x^2 + xy + y^2` is never `2` modulo `4` and is even only for `x, y` even, so `2` is not a norm from `Q(sqrt(-3))` and norms have even `2`-adic valuation; `2 = 1 + 1`, `3 = 1 + 1 + 1` and `4` are norms where the lemma on the discriminant of the new part needs them |
| `cyclic_vg_counts` | `T_d(k)` by a recursion equals the enumeration for `(d, k) = (3, 6), (4, 6), (6, 4)`; `T_4(6) = 141`, `T_6(6) = 1751`, `T_4(8) = 1107`, `T_6(8) = 38165`; the formula of the very general theorem equals a direct count of the characters for `(d, N, r) = (4, 5, 4), (3, 6, 4), (6, 4, 2)` and gives `142, 988, 3950, 1108, 1752, 12258, 38166` |
| `cyclic_nonsplit_example` | `(1, 1, 2, 2, 3, 5, 5, 5)` modulo `6` has sum `0`, order `6`, `p = q = 3` and one coordinate `3`: a character whose abelian sixfold is of non-split Weil type |
| `efour_three_targets` | every piece of `E_0^8` has `18`, `24`, `21` partners of its parity differing in `2`, `3`, `4` coordinates, with groups `H^5` of dimensions `64` (six times) and `16` (twelve times), `16`, and `0`, adding up to `960`; `32 * 960 = 30720` and `40960 - 30720 = 10240 > 104`: the targets of the three-shift theorem |
| `efour_three_degrees` | with `p` at any rank and `delta = 1, 2`, every pair of runs through distinct multiples, not both empty, gives `Ext` degree `3 + delta - U + 7D` different from `3` when `c = e`, from `0` when `e` is above `c` and from `8` when `e` is below `c`: the case analysis of the three-shift theorem |
| `efour_three_spectrum` | the character sums of the weighted Cayley graph of the targets are real and take the values `960, 384, 192, 96, -32, -64, -128, -192`; `64 (960 + 192) / 4 = 18432`, the split `zeta_3 zeta_4 in {1, i}` has weight `18432` in both parities, and `40960 - 18432 = 22528` |
| `efour_spread_ratios` | the ratios of sum `0` modulo `4` that move every coordinate are `21`; the `13` with an entry `2` (a coordinate moved by `-1`) have `D = 256` once and `64` twelve times, `1024` in all, and the other `8` have `D = 16`: the groups of spread two |
| `efour_spread_parity` | for each of the `13` and every set `K` of coordinates with even exponent sum over `K`, that sum is not `2 (|K| - 1)` modulo `4`, while each of the other `8` attains it for some `K`: the last step of the spread-two lemma, and why the entry `-1` is needed |
| `efour_cut_bound` | the `13` ratios generate the `64` ratios of sum `0` in three steps; `|H| (1024 - 256 - 64 (|H| - 2))` is `1536, 2560, 3072` for `|H| = 2, 4, 8`, and `64 |H| >= 1024` for `|H| = 16, 32`: the stabiliser bound for the cuts |
| `efour_spread_three_counts` | between every piece and the `64` of the other parity the groups `H^5` add up to `1072` and the groups `H^7` to `16`; `4 * 60 + 12 * 16 + 4 * (64 + 6 * 16) = 1072`, `64 * 1072 - 128 * 8 = 67584`, `64 * 16 = 1024`: shifts three and five apart |
| `efour_five_values` | with one parity at values in `{0, 2, 4}` and the other in `{1, 3}`, every pair of occupied sets is covered by adjacent single shifts, one parity at two values two apart or three, single shifts three apart, or a gap of four beside a single shift; within six values exactly `([0], [5])` and `([0, 4], [1, 5])` are left |
| `efour_cup_kernel_counts` | `4 * 4 + 6 * 16 * 4 = 400`, `400 + 3 * 28 = 484`, `131 * 28 = 3668`, `3584 - 400 = 3184`, `484 - 104 = 380`, and the pieces take `4` values in each coordinate and `16` in each pair: the cup products on the diagonal at `n = 4` |
| `efour_run_drops` | a run from a piece through one, two or three distinct multiples to a piece lowers the shift by `4, 5, 6, 12, 13` or `20`, for every rank of `p`, and never by `7`: the footnote to the lemma on the diagonal at a lonely shift |
| `efour_lonely_degrees` | for odd `g` from `5` to `31`, `X` in `{0, g}` and runs with `U` steps up and `D` down, `1 <= U + D <= 3`, the degree `3 + X - U + 7D` of a term on a diagonal class is `0` or `8` only if `X = 0` and `U + D = 3`, or `X = 7`, `D = 0`, `U = 2`; with no run it is at least `8` |
| `efour_lonely_residues` | along three steps of `+1` or `-7` the four shifts are pairwise incongruent modulo `4`; for every rank of `p` the four paths of the lemma give four patterns of shifts of the multiples, none shared by two shifts at an odd distance below `40`: the proposition on single shifts |
| `efour_interleaved_cut` | the `28` ratios that move three coordinates and change the parity weigh `640` (`16` twenty-four times, `64` four times) and generate the `128` ratios in three steps; the bounds `1152, 1792, 2688, 3328, 1024, 1024` for `|H| = 2, 4, ..., 64` exceed `640`: the proposition on interleaved shifts |
| `efour_six_values` | with one parity at values in `{0, 2, 4}` and the other in `{1, 3, 5}`, every pair of occupied sets is covered by the exclusions of Section 47, by single shifts at an odd distance or by the interleaved sets `{s, s - 4}`, `{s - 1, s - 5}`; single shifts at every odd distance up to `41` are covered; `64 * 28 = 1792 > 104` |
| `divisor_profiles` | the Betti numbers of the connected sum of two real `n`-tori have Euler characteristic `0` (odd `n`) and `-2` (even `n`), `2 <= n <= 40`; at `n = 5` they are `1, 10, 20, 20, 10, 1`; for `5 <= n <= 16`, eight `d` and `0 <= a <= 3`, `|b| <= 3`, the profile of part (i) of the proposition on sheaves on divisors meets every condition |
| `divisor_endo_positive` | `r^2 (20 d + 1) + 6 < 32 r^2 d^2` for all `d, r >= 1`, so `6 chi(End_0 G) > 0` at `n = 5` |
| `divisor_rank_two_mod3` | `3` divides `2 (d + 1)` exactly when `d = 2` modulo `3`, for every `d` |
| `hh_annihilator_small` | for `n = 1, 2, 3` and every monomial of `HH^*`: the mixed monomials kill `alpha_+` and `alpha_-`, the pure ones send one of them to distinct monomials, so `dim Ann_{HH^k}(omega) = C(4n,k) - 2 C(2n,k) + [k = 2n]`; `n^2` mixed wedge products in degree two |
| `polarised_number_three` | at `n = 3`, fourteen characters `sum c_k theta^k + u alpha_+ + conj(u) alpha_-`, two of each Hankel rank `rho`: the annihilator in `HT^2` has dimension `n^2 (4 - rho)` and contraction rank `(4 + rho) n^2 - 2n`, by exact annihilating vectors and independent images modulo `998244353` |
| `polarised_number_four_rho0` | the same at `n = 4` for the pure Weil character: annihilator `64`, rank `56` |
| `polarised_number_four_rho1` | `n = 4`, `e^theta` plus the Weil part: annihilator `48`, rank `72` |
| `polarised_number_four_rho2` | `n = 4`, `theta` plus the Weil part: annihilator `32`, rank `88` |
| `polarised_number_four_rho3` | `n = 4`, a general integral polynomial part: annihilator `16`, rank `104` |
| `weil_product_formula` | `d^n c_n(t) = d^(2n-t) delta^t` in `Z[delta]`, `delta = sqrt(-d)`, where `c_n(t)` is the coefficient of a monomial `w^(T)`, `|T| = t`, in the Weil class: `eq:omegaprod`, for seven fields and `n <= 10` |
| `weil_multiplicative_coefficients` | `c_(n1)(t1) c_(n2)(t2) = c_(n1+n2)(t1+t2)` for seven fields and `n1, n2 <= 6`: the Weil class of a product is the product of the Weil classes, coefficientwise |
| `weil_multiplicative_exterior` | in the exterior algebra over `Z[sqrt(-d)]`, with signs: `prod_j (d x_j + delta y_j) = d^n omega` for `n <= 3`, and the product of the classes of the factors of every composition of `n` is the class of the product, for `n <= 3` at five fields and for the eight compositions of `4` at `d = 1, 3` |
| `split_member_closed_form` | on the split member `n! omega = (-1)^(n(n-1)/2) (gamma + delta ell)^n` for `n <= 3` |
| `secant_chern_recursion` | the three-term recursion for the Chern classes of a secant character is Newton's identities, for `k <= 8` |
| `secant_discriminant` | the discriminant of the secant recursion is the norm `a^2 d + b^2`, positive unless `a = b = 0` |
| `secant_rank_one_chern` | at `a = 1`: `gamma_2 = b^2 + d`, `gamma_3 = b (b^2 + d)`, `gamma_4 = (b^2 + d)(b^2 - 3d)` |
| `weil_plane_gram` | the Weil classes are primitive and the rational Weil plane has Gram matrix `(-1)^n 2^(2n-1) diag(d^n, d^(n-1))` |
| `lattice_secant_moments` | the binomial moments of `a u + b v` against the lattice spanned by the `e^(j Theta)` |
| `lattice_u3v_moments` | the moments of `u + 3v` are integral exactly when `24` divides `-12 (d + 3)`, `24` and `(d + 9)(d - 2)` |
| `lattice_u3v_criterion` | for every `d`: `u + 3v` lies in the lattice exactly when `d = 15, 23 (mod 24)` |
| `lattice_moments_d3` | at `d = 3` the moments of `u + v` are `(1, 1, -2, 4/3, -1/2)`, least common denominator `6` |
| `lattice_smooth_support` | `ch(O_S) = (0, 0, 2N, -12N, 4N(18 - N))` is not in the lattice for `N = 5, ..., 8` |
| `burch_rank_one_c4` | rank one: `c_1(E) = -b/3` is forced and then `72 c_4(G) = -(b^2 + d)(b^2 + 9d) < 0` |
| `burch_rank_two_c4` | rank two: `24 c_4(G) = gamma_2 (b^2 - 3d + 4ab + 6m)`, and `chi(E) = a^4 - 2 a^2 m + m^2/2` is an integer exactly when `m` is even |
| `burch_rank_two_parity` | for every `d`: `12` divides `3d + 3` exactly when `d = 3 (mod 4)`, so at `b = 3` rank two data need `d = 3 (mod 4)` |
| `jacobian_ring_counts` | the coefficients of $(1+s+\dots+s^{d-2})^{n+2}$ agree with inclusion and exclusion, are symmetric and add up to $(d-1)^{n+2}$, and the Euler number of a hypersurface agrees with its two closed forms, for $n\le8$, $2\le d\le8$, Proposition 20.44 |
| `sextic_fourfold_hodge` | the sextic fourfold has primitive Hodge numbers $1,426,1751,426,1$, Euler number $2610$ and $b_{4}=2606$; $h^{4,0}=\binom{d-1}{5}$ for $3\le d\le7$, zero exactly in the Fano degrees, Remark 20.45 |
| `blowup_sextic_hodge` | $\mathrm{Bl}_{Y}\mathbb{P}^{6}$, for a sextic fourfold $Y$ in a hyperplane, has $(h^{6,0},h^{5,1},h^{4,2},h^{3,3})=(0,1,426,1753)$, Hodge symmetry, only even cohomology, $h^{p,0}=0$ for $p>0$ and total Betti number $2617=e(\mathbb{P}^{6})+e(Y)$, Remark 20.45 |
| `blowup_retrieval` | on a $\mathbb{P}^{1}$-bundle over a base with $H^{*}(Y)=\mathbb{Q}[y]/(y^{5})$, $-\rho_{*}j^{*}j_{*}\rho^{*}a=a$ in every degree and $\xi^{2}=-c_{1}\xi-c_{2}$, for $c_{1}=sy$, $c_{2}=ty^{2}$, $|s|,|t|\le6$, Proposition 20.44 |
| `zero_cycle_degrees` | a class of degree $2p$ on an $n$-fold needs an input only for $2\le p\le n/2$; on a blow-up of a rational sixfold only in degree four on a fourfold centre, and on a uniruled fivefold only in degree four on a fourfold, Proposition 20.44, Remark 20.45 |
| `rigidity_polarisation` | for $n=2,3,4$ the contraction map on $H^{1,1}_{\mathbb{R}}$, of dimension $4n^{2}$, has rank $4n^{2}-1$ and kills the polarisation, Proposition 9.15 |
| `rigidity_norm_kernels` | a norm-character class of rank $r$ has kernel of dimension $n(n-r)$ on the tangent space, for every $r\le n$, $n=2,3,4$, two shapes each, and a class without structure has kernel zero, Proposition 9.15 |
| `object_size_bound` | $\alpha_{\pm}^{2}=0$, $\int\omega_{1}^{2}=2$, and $\chi(E,E)=(-1)^{n}2N^{2}$ for $\operatorname{ch}(E)=r+N\omega_{1}$ whatever $r$, for $n\le4$, Proposition 9.11 |
| `tangent_is_annihilator_two`, `tangent_is_annihilator_three`, `tangent_is_annihilator_three'`, `tangent_is_annihilator_four` | in a second model, for $n=2,3,4$ and several planes: the Weil classes are real of type $(n,n)$, their annihilator in $H^{0,2}$ has dimension $n^{2}$, and $\operatorname{Hom}(P,Q)\to H^{0,2}$ is injective onto it, Lemma 9.6, Theorem 9.17 |
| `tangent_deformations_four`, `tangent_hodge_locus_four` | at $n=4$ the polarised first-order deformations have dimension $36$, the $K$-linear ones $16$, and those killing the Weil line are exactly the $K$-linear ones, Proposition 9.14 |
| `weil_tori_types_two`, `weil_tori_types_three`, `weil_tori_kappa_three` | the Weil classes are of type $(n,n)$ on the whole $K$-linear family, the polarisation only at the balanced member, and $\alpha_{+}\kappa^{n}=0$ for $\kappa$ in $V_{+}\otimes V_{-}$, at $n=2$ ($d=1,3$) and $n=3$ ($d=2$), Setup 17.1 |
| `weil_tori_hodge_two`, `weil_tori_orbit` | a very general Weil torus of dimension four (and six, through the torus orbit of one member) has no Hodge classes in degree $2k$, $0<k<n$, and only the Weil plane in degree $2n$, Lemma 17.2, Lemma 17.3 |
| `hochschild_profile_two` | the Hochschild profile at $n=2$ on the eight shapes, each with $u=1$ and $u=2+3i$: $(1,8,\rho_{2},8,1)$ with $\rho_{2}=12,16,20,24$ as the Hankel rank is $0,1,2,3$, Proposition 17.10 |
| `hochschild_profile_three_pure`, `hochschild_profile_three_cn`, `hochschild_profile_three_generic_low`, `hochschild_profile_three_generic_middle`, `hochschild_profile_three_generic_high` | the profiles at $n=3$ of the pure character, of $c_{3}\theta^{3}$ and of a general shape, $(1,12,57,112,57,12,1)$ for the last, each rank exact by independent images and exact relations, Proposition 17.10 |
| `hochschild_profile_special_two`, `hochschild_profile_special_three`, `hochschild_profile_special_three_second` | for $c_{n}\theta^{n}$ alone the middle rank drops exactly at $|u|=\binom{n}{a}n!\,|c_{n}|$ and only in degree $n$: $\rho_{2}=22,23$ at $n=2$, $\rho_{3}=110$ at $n=3$, Proposition 17.10 |
| `descent_weil_quadratic`, `descent_weil_quartic`, `descent_weil_sextic_one`, `descent_weil_sextic_two` | the map $P$ carries $W_{F}(B\times Y)$ isomorphically onto $W_{F}(B)$ and kills it when the Weil class of $Y$ is replaced by its polarisation, for four imaginary quadratic fields, $\mathbb{Q}(\zeta_{5})$, $\mathbb{Q}(\zeta_{8})$ and $\mathbb{Q}(\zeta_{7})$, Proposition 20.13 |
| `descent_discriminant` | $H_{B}+\operatorname{diag}(1,-t)$ has signature $(n+1,n+1)$ and $t$ times the discriminant of $H_{B}$, for $n\le5$ and five values of $t$, Proposition 20.13 |
| `descent_scalar_extension` | $j^{*}W_{F}(B_{F})=W_{K}(B)$ for $\mathbb{Q}(i)\subset\mathbb{Q}(\zeta_{8})$, $\mathbb{Q}(\sqrt{-7})\subset\mathbb{Q}(\zeta_{7})$ and $\mathbb{Q}(\sqrt{-3})\subset\mathbb{Q}(\zeta_{9})$, $n=1,2$, Proposition 20.13 |
| `wirtinger_volumes`, `wirtinger_primitive`, `wirtinger_pairings` | on a Mumford square, $\theta^{4}=24\,\mathrm{vol}$, $\theta_{Y}^{8}=8!\,\mathrm{vol}$, the decomposition $\wedge^{2}V=\mathbb{C}\theta+U_{12}+U_{13}+U_{23}$ into primitive pieces, and the pairings $\int\pi_{0}\theta_{Y}^{6}=2880$, $\int\pi_{ij}\theta_{Y}^{6}=0$, $L(\theta_{Y}^{2})=56$, Example 20.79 |
| `mumford_motivic_sp`, `mumford_motivic_irreducible` | $\mathfrak{g}=\mathfrak{sl}_{2}^{3}$ and the $27$ products span $\mathfrak{sp}(V,\psi)$, of dimension $36$; $P$ is irreducible, and $S^{2}V$ is the sum of four irreducible summands, Proposition 21.47 |
| `mumford_motivic_permutations`, `mumford_motivic_commutant` | the six permutations of the factors lie in $\operatorname{Sp}(V,\psi)$ and permute the factors of $\mathfrak{g}$; the commutant of $\mathfrak{g}$ is the scalars; the subgroups of $S_{3}$ stable under $A_{3}$ are $1$, $A_{3}$, $S_{3}$, Proposition 21.47 |
| `mumford_motivic_projectors`, `mumford_motivic_cycle` | in the model of item (LX) the projectors $\pi_{0},\pi_{12},\pi_{13},\pi_{23}$ are idempotents of traces $1,9,9,9$, hence of these ranks, and $\zeta$ fixes $\pi_{0}$ and carries $\pi_{12}$ to $\pi_{23}$, $\pi_{23}$ to $\pi_{13}$, $\pi_{13}$ to $\pi_{12}$, Setup 21.18 |
| `mumford_motivic_hyperdeterminant`, `mumford_motivic_weyl` | Cayley's hyperdeterminant is invariant under $G$ and the permutations but not under $\operatorname{Sp}(V,\psi)$; $\dim(S^{4}V)^{G}=1$ and $\dim(S^{4}V)^{\operatorname{Sp}}=0$, Proposition 21.47 |
| `mumford_motivic_invariants` | the non-crossing pairings give bases of the invariants, $1,8,125$ products over the factors, with $4,45$ orbits of $A_{3}$ and $4,35$ of $S_{3}$, and the pairings of $\psi$ have Gram matrices of ranks $1,3,15$, Proposition 21.48 |
| `mumford_three_adic_anisotropic` | $\langle6,-2,-2\rangle$ has no primitive zero modulo $27$, so it is anisotropic over $\mathbb{Q}_{3}$, Remark 21.5 |
| `k3_hilbert_square_betti`, `k3_fujiki_determinant`, `k3_riemann_roch`, `k3_partition_sizes` | the Betti numbers $(1,0,23,0,276,0,23,0,1)$ of $S^{[2]}$; the determinant of the Fujiki pairing on $\mathrm{Sym}^{2}H^{2}$, $2^{46}\cdot25$; $\int c_{2}^{2}=828$ and $\chi(L)=\binom{q(L)/2+3}{2}$; and the least $n$ with $t$ distinct part sizes, $t(t+1)/2$, Proposition 20.39, Proposition 20.40 |
| `sextic_lattice_fields`, `sextic_lattice_euler_even`, `sextic_lattice_shapes`, `sextic_lattice_exp_classes` | the sixteen cubic fields of the cases; $\chi(v,v)$ is even; $r^{3}-2r^{2}\le4$ on every support and rank pattern, with equality only at $(54,112)$; and the two classes $\operatorname{Re}e^{i\theta}$, $\operatorname{Im}e^{i\theta}$, Proposition 19.49 |
| `sextic_lattice_case_00`, `sextic_lattice_case_01`, `sextic_lattice_case_02`, `sextic_lattice_case_03`, `sextic_lattice_case_04`, `sextic_lattice_case_05`, `sextic_lattice_case_06`, `sextic_lattice_case_07`, `sextic_lattice_case_08`, `sextic_lattice_case_09`, `sextic_lattice_case_10`, `sextic_lattice_case_11`, `sextic_lattice_case_12`, `sextic_lattice_case_13`, `sextic_lattice_case_14`, `sextic_lattice_case_15`, `sextic_lattice_case_16`, `sextic_lattice_case_17`, `sextic_lattice_case_18`, `sextic_lattice_case_19`, `sextic_lattice_case_20`, `sextic_lattice_case_21`, `sextic_lattice_case_22`, `sextic_lattice_case_23`, `sextic_lattice_case_24`, `sextic_lattice_case_25`, `sextic_lattice_case_26`, `sextic_lattice_case_27`, `sextic_lattice_case_28`, `sextic_lattice_case_29`, `sextic_lattice_case_30`, `sextic_lattice_case_31`, `sextic_lattice_case_32`, `sextic_lattice_case_33`, `sextic_lattice_case_34`, `sextic_lattice_case_35`, `sextic_lattice_case_36`, `sextic_lattice_case_37`, `sextic_lattice_case_38`, `sextic_lattice_case_39`, `sextic_lattice_case_40`, `sextic_lattice_case_41`, `sextic_lattice_case_42`, `sextic_lattice_case_43`, `sextic_lattice_case_44`, `sextic_lattice_case_45`, `sextic_lattice_case_46`, `sextic_lattice_case_47` | for each of the $48$ pairs of a field and $q$: the integral classes of $S(0,q)$ are the span of the recorded basis, with the recorded Gram matrix of $-\chi/8$, Proposition 19.49 |
| `sextic_weil_units`, `sextic_weil_imaginary`, `sextic_weil_shape_classes`, `sextic_weil_least_values` | the units with $2+a=\beta^{2}$; the twenty cases in which $F$ contains an imaginary quadratic field; the classes of least norm with an $F$-Weil part; and the least values of $-\chi$, $192$ only over $\mathbb{Q}(\zeta_{7})^{+}$ at $q=3+a$, Lemma 19.50; the least values are not used in the paper |
| `sextic_weil_scan_0`, `sextic_weil_scan_1`, `sextic_weil_scan_2`, `sextic_weil_scan_3`, `sextic_weil_scan_4`, `sextic_weil_scan_5`, `sextic_weil_scan_6`, `sextic_weil_scan_7` | the scans of the lattices by fraction-free Schur complements: no integral class with $-\chi\le24$, and the least $-\chi$ with an $F$-Weil part as recorded, beyond Proposition 19.49 and not used in the paper |
| `fm_powers_computed` | $\Phi_{\mathcal{P}}(\theta^{\prime k})=(-1)^{g(g+1)/2+k}\frac{k!}{(g-k)!}\theta^{g-k}$, computed in the exterior algebra of $V\oplus V^{\vee}$ for $g\le4$, Theorem 6.5 |
| `mumford_routes_target_open`, `mumford_routes_equivalent`, `mumford_routes_minimal`, `mumford_routes_stronger`, `mumford_routes_conjecture` | the Horn system of the routes to the Mumford target: it is closed and the target is not proved; its equivalent forms; the twelve minimal routes; the stronger routes; and the minimal sets $\{\mathrm{HC}\}$, $\{F_{3}\}$, $\{L,M\}$ yielding the Hodge conjecture, Corollary 21.45, Proposition 20.33 |
| `targets_invariant_dims`, `targets_invariant_ring` | the invariants of $\mathfrak{sl}_{2}^{3}$ on $X\times X$ have dimensions $1,0,3,0,8,0,16,0,28,\dots$, and are generated in degrees two and four with two exceptional classes, Theorem 20.29 |
| `targets_cm_counts`, `targets_cm_generation`, `targets_two_branches` | at a CM point the Hodge classes number $1,0,16,0,132,\dots$ on $X_{c}\times X_{c}$ and are generated by divisor classes and pull-backs; the two branches of classes killed by $Q\,HH^{1}$ and $P\,HH^{1}$, Theorem 20.29, Corollary 20.30 |
| `lefschetz_pontryagin`, `lefschetz_family_operator` | the Lefschetz operator is a Pontryagin product on ten types of polarisation, and $[L,\Lambda]=H$ for the operator of the theorem on four product families, Proposition 20.20, Theorem 20.21 |
| `split_resolution_data` | the scalar $(e^{2}+d)/2$ is positive, the vanishing degrees of $H^{*}(\mathcal{O}(m\Theta))$ exclude $2$, the three resolutions are minimal and secant, and no Koszul resolution in the box is secant, Theorem 18.89, Theorem 18.81 |
| `transport_scaling`, `transport_multiplicity` | $\det\phi=c^{2G}$ and $\phi^{T}E\phi=c^{2}E$ on the samples; the multiplicity is $c^{4}$ on the stable sublattice and smaller on the unstable one, and the lower bound increases strictly, Lemma 16.13, Lemma 16.14 |
| `quaternionic_ratios`, `quaternionic_scaling`, `quaternionic_presentation` | the scale-free ratios of the quaternionic Weil cycle, the growth of its data in $b$ alone, and the change of presentation by $\alpha$, Proposition 16.20 |
| `quaternionic_weil_lattice_0`, `quaternionic_weil_lattice_1`, `quaternionic_weil_lattice_2`, `quaternionic_weil_lattice_3` | for $d=1,2,3,7$ the integral Weil lattice has Gram matrix $\operatorname{diag}(8d,8d^{2})$ and the divisor products meet it in a sublattice of index $2(a_{1}a_{2})^{2}$, Proposition 16.20 |
| `divisor_route_rank`, `divisor_route_trace`, `divisor_route_pencil`, `divisor_route_index` | the lattice of $K$-bilinear classes has rank $12$ and signature $(8,4)$; the pencil $\phi_{k}^{2}=(1+k^{2})/(4d^{2})$ with $x_{k}$ primitive; and $\mathbb{Z} x_{k}+\mathbb{Z} x_{k}(i\cdot,\cdot)$ saturated for every $k$, Proposition 16.25 |
| `divisor_route_minimum_one`, `divisor_route_minimum_three` | $N_{k}=\mathbb{Z}\tfrac{1}{2d}\eta\oplus\mathbb{Z} x_{k}\oplus\mathbb{Z} x_{k}(i\cdot,\cdot)$ and the minimum $\mu_{k}=32d^{2}(1+k^{2})$ of $I$ on it off $\mathbb{Q}\eta$, for $d=1,3$ and $k\le10$, Proposition 16.25 |
| `divisor_route_unitary_one`, `divisor_route_unitary_three`, `divisor_route_centraliser_one_0`, `divisor_route_centraliser_one_1`, `divisor_route_centraliser_one_2`, `divisor_route_centraliser_one_3`, `divisor_route_centraliser_one_4`, `divisor_route_centraliser_three_0`, `divisor_route_centraliser_three_1`, `divisor_route_centraliser_three_2`, `divisor_route_centraliser_three_3`, `divisor_route_centraliser_three_4` | the centraliser of $i$ in $\mathfrak{sp}(V,E)$ has dimension $16$, and that of $i$ and $\phi_{x_{k}}$ dimension $10$ with three invariants in $\wedge^{2}V^{*}$, for $d=1,3$ and $k\le4$, Proposition 16.25 |
| `divisor_route_siegel_one`, `divisor_route_siegel_three` | a rational complex structure on the Siegel locus and its brackets span the centraliser, $d=1,3$, Proposition 16.25 |
| `exceptional_mumford_square`, `exceptional_quintic`, `exceptional_annihilator` | two of the eight invariants of $\wedge^{4}(V\oplus V)$ on a Mumford square are exceptional; the adjoint weights of the quintic threefold; and the annihilator of the Weil class in $HT^{2}$ for $n=2,3$, Proposition 20.74, Proposition 20.75, Theorem 16.31 |
| `cm_fields_quartic`, `cm_fields_sextic_seven_two`, `cm_fields_sextic_seven_one`, `cm_fields_sextic_nine` | the base point for $\mathbb{Q}(\zeta_{5})$, $\mathbb{Q}(\zeta_{8})$, $\mathbb{Q}(\zeta_{7})$ and $\mathbb{Q}(\zeta_{9})$: CM type, trace-dual bases, eigenvectors, the alternating form and the closed form of the balanced classes, Theorem 19.5 |
| `cm_fields_neron_severi`, `cm_fields_composite` | $\mathrm{NS}$ has dimension $32$ at the base point for $\mathbb{Q}(\zeta_{5})$, $n=2$; and $W_{K}$ lies in the span of the products of pairs of $W_{F}$ for $\mathbb{Q}(i)\subset\mathbb{Q}(\zeta_{8})$, Proposition 19.10 |
| `mumford_rm_isotypic`, `mumford_rm_isotypic_mixed`, `mumford_rm_isotypic_diagonal`, `mumford_rm_image` | $\wedge^{2}V$ has four summands of multiplicity one, the image of $\mu$ fills each, $h^{2,0}=6$, and the Hodge numbers of the pieces, Lemma 21.3, Proposition 21.2 |
| `mumford_rm_pairing`, `mumford_rm_adjoint_one`, `mumford_rm_adjoint_two` | the Lefschetz pairing and the trace form agree up to scale, and $4\mu\mu^{\dagger}$ acts by scalars on the pieces, Proposition 21.2 |
| `mumford_rm_spin`, `mumford_rm_kuga_satake` | the spin lifts, thirty-two vectors of highest weight $(1,1,1)$, and the Kuga–Satake map, with $N_{i}$ anticommuting and squaring to $4,8,20$, Proposition 11.7, Theorem 21.4 |
| `twistor_real_structure`, `twistor_quaternion`, `twistor_pieces`, `twistor_exchange` | the real structure and the three complex structures of a Mumford square, the quaternion that rules out a polarisation at $J_{1}$, and the types and exchange of the tensors $\pi$, Proposition 21.24 |
| `twistor_invariant_one`, `twistor_invariant_two`, `twistor_annihilator_first`, `twistor_annihilator_third` | $\omega$ is invariant, and its annihilator at $J_{1}$ and $J_{3}$ is one line, Proposition 21.24 |
| `hk_iota`, `hk_isotypic`, `hk_products`, `hk_octic` | the map $\iota$ and the symplectic form, the isotypic pieces of $H^{2}(X\times X)$, the exceptional classes as products, and the octic form, Proposition 21.25 |
| `semireg_monomials`, `semireg_block` | the six products of $\beta,\widehat\beta,\ell$ are independent and $\eta^{2}$, $\theta^{+}\theta^{-}$ are independent; the multiplication table of one block in its Hodge basis, Lemma 18.3, Lemma 18.1 |
| `semireg_rank_two`, `semireg_rank_three` | the semiregularity map of a sum of line bundles is injective for up to three classes at $n=2$ and ten at $n=3$, and has rank $22<24$ for four classes at $n=2$, Lemma 18.4, Theorem 18.5 |
| `semireg_object_chern`, `semireg_object_rank` | the explicit object: its Chern character, index and Prouhet–Tarry–Escott pair, and the rank $75$ of its semiregularity map, Lemma 18.11, Proposition 18.14 |
| `qk_model`, `qk_closed_form` | the one-place model: the transforms of $X\times0$, the diagonal, the antidiagonal and six graphs, and $\operatorname{ch}\Phi_{j}(T_{j}-P_{j})=-\frac14(\eta_{j}^{2}+\gamma_{j}^{2}-d\ell_{j}^{2})$ as a polynomial identity in $d$, a kernel not used in the paper |
| `qk_su_one`, `qk_su_two`, `qk_su_three`, `qk_su_five_halves`, `qk_su_two_fifths` | integral bases of $\mathfrak{su}_{j}(d)$ for $d=1,2,3,\frac52,\frac25$, Proposition 19.40 |
| `qk_flat`, `qk_eigen_hodge` | the class $\operatorname{ch}\Phi_{j}(T_{j}-P_{j})$ is flat, of pure degree four, with nonzero Weil part and of Hodge type, its twists by $e^{\pm\ell/2}$ are not flat, $\int\eta_{j}^{4}:\int\Omega_{j}^{2}=3:4$, and $\sqrt{-q}$ has eigenvalues $\pm4s_{j}$ on $(\gamma_{j}\mp s_{j}\ell_{j})^{2}$, not used in the paper |
| `qk_contraction_one`, `qk_contraction_one_general`, `qk_contraction_three`, `qk_contraction_three_general` | its contraction map has rank $23$ with a $5$-dimensional kernel in $H^{1}(T)$, against $24$ and $4$ for a general invariant class, at $d=1,3$, not used in the paper |
| `qk_invariants_one_low`, `qk_invariants_one_middle`, `qk_invariants_one_high`, `qk_commutant_one`, `qk_invariants_three_low`, `qk_invariants_three_middle`, `qk_invariants_three_high`, `qk_commutant_three`, `qk_invariants_two_fifths_low`, `qk_invariants_two_fifths_middle`, `qk_invariants_two_fifths_high`, `qk_commutant_two_fifths` | for $d=1,3,\frac25$ the invariants of $\mathfrak{su}_{j}(d)$ have dimensions $1,1,3,1,1$ in degrees $0,2,4,6,8$ and none in odd degree, and the commutant is spanned by $1$ and $\sqrt{-q}$, Proposition 19.40 |
| `qk_graph_classes_one`, `qk_graph_classes_two`, `qk_graph_classes_three`, `qk_graph_classes_four`, `qk_graphs`, `qk_graph_invariants`, `qk_graph_twists` | the classes $(b,a)_{*}(c)$ on seven graphs span a space $L_{j}$ of dimension $24$, and $\Phi_{j}(L_{j})$ meets the invariants exactly in $\mathrm{span}(1,\mathrm{pt}_{j})$, and $e^{B}\Phi_{j}(L_{j})$ exactly in $e^{g\eta_{j}}\mathrm{span}(1,\mathrm{pt}_{j})$ for four $B$, Proposition 19.40 |
| `qk_pure_spinors_one`, `qk_pure_spinors_two`, `qk_pure_spinors_three`, `qk_pure_spinors_four`, `qk_pure_spinors_five`, `qk_pure_spinors_six`, `qk_pure_spinors_seven`, `qk_not_pure` | the transforms of line bundles on seven graphs are pure spinors, also after the twist by $e^{\ell/2}$; at $d=1$ the flat classes $\operatorname{ch}\Phi_{j}(T_{j}-P_{j})$ and $\Omega_{j}$ are not pure, and $(\gamma_{j}-i\ell_{j})^{2}$ is pure over $\mathbb{C}$, Proposition 19.40 |
| `qk_parity_congruences`, `qk_mod_small`, `qk_congruences_large`, `qk_nu_bounds` | $\int x^{2}$ is even for integral classes of degree four on a torus of dimension four; the conditions (a) to (c) leave only $D=3$, $m=1$ among all squarefree $D$; and the bounds on $\nu$, Remark 19.39 |
| `qk_prym`, `qk_prym_bound` | $\varphi(N)=4$ exactly for $N=5,8,10,12$ below $200$, a hyperbolic hermitian form of rank $2n$ has determinant $(-1)^{n}$, and $3g-3<\frac12\varphi(N)(g-1)^{2}$ for all $\varphi(N)\ge4$, $g\ge3$, Remark 19.24 |


## What is not in the certificate

Every computation of the paper is checked in exact arithmetic by
`code/verify_all.py`; the items are those of `COMPUTATIONS.md`. The following
have no Lean counterpart, or only a partial one.

* Outside the reach of a kernel with no libraries: the Macaulay2 computations
  of local Ext algebras and jet classes, items (XXIX), (XXXI), (XL) and the
  local part of (LXVIII); the evaluation of theta integrals in ball
  arithmetic, part (H) of item (LXXII); and the sign-pattern search of item
  (XXII), of up to `4.29 * 10^14` patterns. The parts of items (LXXII) and
  (LXXIII) that run in double precision certify nothing on their own.
* Parts of items whose exact linear algebra is otherwise in Sections 56 to
  81: the exhaustive searches of item (XIII); the other five shapes at
  `n = 3` and the longer run at `n = 4, 5` of item (LIII); parts (A) to (C)
  of item (LVIII), identities in the exterior algebra on twenty-four
  generators; parts (B) to (D) of item (LIX), which work over both places of
  explicit number fields; part (F) of item (LX), the invariance of classes of
  `X x X` and `X x X x B` under `sl(V)`; and parts (D) and (F) to (H) of item
  (LXI), identities at random rational points, invariants of orthogonal
  groups, spans in CM fields of degree up to ten, and the cohomology of
  generalised Kummer varieties sector by sector.

The data blocks of the certificates are written by the scripts in
`generate/`, each from the model of the corresponding program in `code/`:
`make_section51.py` for Section 51, and for Sections 56 to 81
`make_tangent.py`, `make_weil_tori.py`, `make_profile.py`, `make_descent.py`,
`make_wirtinger.py`, `make_k3.py`, `make_sextic_lattice.py`,
`make_targets.py`, `make_quaternionic.py`, `make_divisor_route.py`,
`make_cm_fields.py`, `make_mumford_rm.py`, `make_twistor_locus.py`,
`make_semiregularity.py` and `make_quartic_kernels.py` (with the shared
helpers of `emit.py`). Run from the repository root, each prints the data
block of its section.

## Two statements that look true and are not

The natural witness `tau = 1 + sqrt(-d)` for the lemma separating the
characters does not work at every field. At `d = 1` the ratio
`tau/conj(tau)` is `sqrt(-1)`, a primitive fourth root of unity, and at
`d = 3` it is a primitive cube root of unity, so at those two fields the
characters agree at that particular `tau`. The lemma is true, but not by that
route, which is why the proof in the paper uses only the finiteness of the
group of roots of unity of `K`. `bad_witness` records the failure.

The exceptional set at `d = 3` is `3 | n`, not `6 | n`; `bad_witness_exceptions`
records the correct condition.

Neither affects the truth of the theorem, and both are the kind of slip that a
careful reading does not catch and a kernel check does.

## Companion scripts

`code/verify_all.py` in the parent directory performs the same checks in exact
rational arithmetic over Q, independently of Lean, together with the exterior
algebra computations that Lean does not carry, and prints
`2218 checks passed, 0 failed`.

## Transcript

`axioms.txt` is the unedited output of `lean HodgeObstruction.lean` under
Lean 4.34.0 (x86_64 Linux, commit 293d5d0c): four hundred and nine lines, one per
theorem, one hundred and twenty-eight reading `does not depend on any axioms` and two hundred and eighty-one reading
`depends on axioms: [propext]`, exit status 0, no `sorryAx`. `lake build`
completes with the same report.
