# Algebraic Loci of Weil Classes on Abelian Varieties

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22950275.svg)](https://doi.org/10.5281/zenodo.22950275)

The complete LaTeX source of the paper *Algebraic Loci of Weil Classes on
Abelian Varieties*, with its figures and the compiled PDF, and the
verification code that accompanies it. The paper proves every statement in
its text; the programs here repeat its finite arithmetic as an independent
check, and some of them record data that the paper does not use.

Release v5.0.1 accompanies the current version of the paper, which cites this
archive by its Zenodo DOI. Zenodo archives each GitHub release under its own
version DOI, and gathers all of them under one concept DOI:

| | DOI |
| --- | --- |
| release v5.0.1 (version DOI) | 10.5281/zenodo.23225483 (https://doi.org/10.5281/zenodo.23225483) |
| release v5.0.0 (version DOI) | 10.5281/zenodo.23221435 (https://doi.org/10.5281/zenodo.23221435) |
| release v4.0.0 (version DOI) | 10.5281/zenodo.23197107 (https://doi.org/10.5281/zenodo.23197107) |
| release v3.2.0 (version DOI) | 10.5281/zenodo.23093099 (https://doi.org/10.5281/zenodo.23093099) |
| release v3.1.1 (version DOI) | 10.5281/zenodo.23078541 (https://doi.org/10.5281/zenodo.23078541) |
| release v3.0.0 (version DOI) | 10.5281/zenodo.23047883 (https://doi.org/10.5281/zenodo.23047883) |
| release v2.0.0 (version DOI) | 10.5281/zenodo.23038895 (https://doi.org/10.5281/zenodo.23038895) |
| all versions (concept DOI) | 10.5281/zenodo.22950275 (https://doi.org/10.5281/zenodo.22950275) |
| release v1.0.0 (version DOI) | 10.5281/zenodo.22950276 (https://doi.org/10.5281/zenodo.22950276) |

Cite the version DOI of the release you used, or the concept DOI for the
project as a whole.

Everything here is self-contained. Nothing needs a network connection, a
licence, or a package other than those named below.

## Layout

    COMPUTATIONS.md  every computation, item by item, with the results of the
                paper that it checks (the paper cites the archive as [BMB26]);
                code/computations/make_computations.py rebuilds it
    code/       exact-arithmetic verification in Python 3 (sympy for secant_plane.py,
                weiltype_family.py, mumford_rigidity.py, mumford_object.py,
                lefschetz_closure.py, twistor_locus.py and hk_pullback.py, numpy
                integer arrays for pte_remaining.py and weil_tori.py, and
                python-flint exact rational matrices for attack_checks.py;
                fourfold_certified.py works in ball arithmetic (Arb, through
                python-flint), so its rank is proved; fourfold_products.py
                and two parts of diagonal_ci.py work in double precision and
                check statements proved or certified otherwise)
    code/attack/  the attack scripts of item (LV), with their verifiers' scripts
                and transcripts (item (LV))
    code/extreme/ longer runs of several items, with transcripts
    verify.ps1  the whole verification on Windows, Python suite then Lean
    lean/       a kernel-checked certificate of the finite arithmetic, Lean 4
    notes/      working notes beside the paper, each with its own programs:
                notes/fourier_mukai/ excludes the exponential characters of
                rank 88 at a quartic CM field whose inverse exponent lies in
                an explicit lattice; notes/route/ corrects the route note on
                Hilbert-Burch resolutions of secant supports on abelian
                fourfolds (neither is part of verify_all.py)
    figures/    the generators and TikZ sources of every figure in the paper
    tex/        the whole LaTeX source of the paper: main.tex, preamble.tex,
                sections/, appendices/, bibliography.tex, declarations.tex
                and figures/ (a copy of figures/ above, with the PDF and PNG
                of every figure); latexmk -pdf main.tex, run in tex/ with
                a standard TeX Live, builds tex/main.pdf, which is included
    main.pdf    a copy of the compiled paper tex/main.pdf

## Running the verification

    cd code
    python3 verify_all.py

On Windows, `verify.ps1` at the top level runs the same suite and then the
Lean check:

    powershell -ExecutionPolicy Bypass -File .\verify.ps1

The last lines are

    2218 checks passed, 0 failed
    overall: PASS

and the exit status is zero. The driver runs five self-contained checks and
then calls the companion scripts in the same directory:

| script | what it settles |
| --- | --- |
| `verify_all.py` | the Fourier-Mukai transform on powers of the polarisation, the permutation sign, the character grading, the secant count, the semiregularity target |
| `explicit_weil.py` | the coordinate model of Weil type and the two generators of the Weil line |
| `fm_theta.py`, `fm_sign.py` | standalone reruns of items (I) and (II): the transform on powers of the polarisation with the closed form, and the permutation sign up to g = 12; not called by the driver |
| `hodge_invariants.py` | the count of Hodge classes by invariant theory |
| `kugasatake.py` | the Clifford algebra and the reach of the Kuga-Satake construction |
| `weiltype_family.py`, `secant_plane.py` | the family of Weil type and the secant plane |
| `split_locus.py` | the split member and the closed form of its Weil line |
| `split_geometry.py` | the polarisation of the split member (with the eigenvalue check that fixes the convention for the K-action), its discriminant, codimension and divisors |
| `quaternionic.py` | quaternionic multiplication, a base point in every Weil family, and the dimension of the quaternionic locus |
| `semiregularity.py` | the semiregularity map of a sum of line bundles, the positivity obstruction, and the explicit object at n = 3 |
| `semireg_fast.py` | the same ranks modulo a prime, which reaches n = 3 |
| `weil_annihilator.py` | the annihilator of the Weil line in H^{0,2} has dimension n^2, the parity split of the semiregularity map, and the uniform kernel over the whole family |
| `lagrangian_locus.py` | the quaternionic locus as a Lagrangian Grassmannian, and that the real loci sweep the family |
| `integrality.py` | that nothing numerical forbids the object the secant construction needs: the Chern classes are integral and Bogomolov never binds |
| `rigidity.py` | infinitesimal rigidity: the polarisation is the only class that survives the family, and a norm-character class of rank r cuts codimension n.r |
| `object_size.py` | the Riemann-Roch bound on the size of any object carrying the Weil class |
| `weil_product.py` | the Weil class is multiplicative under products, and the base case in every dimension |
| `weil_tangent.py` | the annihilator is the tangent space to the Weil family, over the Gaussian rationals |
| `secant_exists.py` | that a coherent sheaf with the Chern character the secant construction needs exists in every dimension, with an explicit witness in line bundles and the least multiple M |
| `pte_search.py` | which split objects supported on R can be semiregular: the level sums, the level sets that survive them at n = 3, and the exhaustive search that removes them |
| `smooth_support.py` | the invariants a smooth support must have, read off the Chern character, and the Bogomolov-Miyaoka-Yau bound that leaves four discriminants |
| `hilbert_burch.py` | Cohen-Macaulay supports with a split resolution: the complete intersections are excluded outright, ranks two and three are empty, and the candidates at higher rank are printed |
| `closure_graph.py` | the logical skeleton of the paper and of the literature it quotes as a rule set: the conjecture is not in the closure of what is proved; the conjecture for varieties that are not abelian, (F3), gives it for every abelian variety A through A x P^1 and so is the conjecture itself; with (F3'), the conjecture modulo abelian varieties, added, there are exactly five minimal sufficient sets, {(F3)}, {Lefschetz standard conjecture B, every Hodge class motivated}, {B, (F3')}, {variational Hodge conjecture for algebraic classes, (F3')} and the route of the paper {(P2), (F2), (F3')}; (F3') alone gives nothing on abelian varieties; without the two additions the search returns four sets; and the secant route lies in no minimal set |
| `hochschild_annihilator.py` | the annihilator of a Weil class in the whole exterior algebra HH^*(A) of dimension 2^{4n}: that HH^1 splits as P + Q with P and Q the annihilators of the two conjugate pieces of the class, each of dimension 2n; that the degree-two annihilator is exactly P ^ Q, of dimension 4n^2; the dimension binom(4n,k) - 2 binom(2n,k) in every degree with one extra class at k = 2n; the codimension 2^{2n+1} - 1 of the ideal generated; and the unconditional lower bound dim Ext^2(E,E) >= 2n(2n-1) |
| `p2_support.py` | the finite linear algebra of the numerical form of the semiregularity criterion and of the support theorem: the rank 2n(2n-1) of contraction into the Weil class on HH^2 and its injectivity on wedge^2 P + wedge^2 Q, the class of a point on a torus contracted with a ^ b, the dichotomy in the normal space, the eigenspace bookkeeping in an explicit rational model over Q(i), and the separation of the Weil line from the classes pulled back from quotients by abelian subvarieties tangent to an eigenspace |
| `lefschetz_family.py` | the Lefschetz standard conjecture for the total space of an abelian scheme over a curve with algebraic invariant cycles: on abelian varieties with g <= 4 the operator Lambda equals D^{-1} times the Pontryagin product with l^{g-1}/(g-1)!, computed from mu_* and mu^*; on product families the operator assembled from the relative and base parts satisfies [L, Lambda] = H; and the invariants of the Mumford group in wedge^q V are 1,0,1,0,1,0,1,0,1 |
| `targets_reduction.py` | the two remaining targets reduced to one case of the Lefschetz standard conjecture each: the invariant ring of the square of a Mumford fourfold is generated in degrees 2 and 4; at a CM point every Hodge class of X_c x X_c lies in the ring generated by divisor classes and pull-backs of Hodge classes of X_c, so the Hodge conjecture holds there; and the (p,p) classes annihilated by Q^HH^1, P^HH^1, HH^1^HH^1 are C alpha_-, C alpha_+, 0 |
| `mumford_rigidity.py` | the rigidity of the exceptional classes on the square of a Mumford fourfold: the nine weight blocks of the Siegel tangent space sp^{-1,1} (36) and the 46 blocks of HT^2 = 28 + 64 + 28 by type, weight and exchange parity; every Gram determinant of contraction into omega_a is a positive constant times a product of sums of squares, positive definite forms and linear forms with certificates; the only generic kernel is the derivation of the Mumford curve; the hyperplane a0+a1+a2+a3 = 0 is the one exception, in the bivector blocks; so the annihilator is one dimensional and the numerical criterion is dim Ext^2 = 119 |
| `mumford_object.py` | what a perfect complex with the Chern character of an exceptional class on a Mumford square must look like: the ranks of contraction into the class on HT^k are 1, 16, 119, 328, 560, 328, 119, 16, 1 (exact over Q at a sample point, and modulo a prime at a rational class for the cubic subfield of Q(zeta_7)), symmetric as the duality lemma predicts; chi(E,E) = 0 then forces at least 800 dimensions of odd self-extensions; and at a CM point the products of divisor classes span 100 of the 132 Hodge classes in degree four and miss every exceptional class |
| `lefschetz_closure.py` | what line bundles generate on a Mumford square: the Sp(V, psi)-invariants of wedge^k(V+V) are 1,3,6,10,15,10,6,3,1 and are spanned by products of the three divisor classes; the Hodge classes that are not Lefschetz number 0,0,2,6,13,6,2,0,0; at a CM point the Lefschetz group is the diagonal torus, whose invariants 1,16,100,304,454,... are products of the 16 divisor classes; omega_a is invariant under that torus only when a1 = a2 = a3; and the Sp-module generated by an exceptional class is irreducible of highest weight 2 varpi_2 and dimension 308 |
| `twistor_locus.py` | the Hodge locus of an exceptional class among all complex tori: V_R as the fixed space of the real structure that is quaternionic on the two compact factors and real on the third; psi(x, Jy) has signature (0,8) for the complex structures of the Mumford family and (4,4) for a unit quaternion j of a compact factor; the quaternion k with kj = -jk carries psi(x, Jy) to its negative, so no invariant class of degree two polarises a member of the twistor line; the annihilator of omega_a in H^1(T) (dimension 64) is one dimensional at both kinds of point, the direction of the curve and the direction of the twistor sphere; and the exchange of the first and third factors relates the two computations |
| `hk_pullback.py` | the square of a Mumford fourfold as a holomorphic symplectic variety: iota(x) = (x (x) 1) Psi embeds T = Lie G in H^1 (x) H^1; the Casimirs split H^2 (dimension 120) into pieces of dimensions 3, 27, 27, 27, 27, 3, 3, 3 with (2,0)-parts 0, 0, 9, 9, 9, 0, 0, 1, so iota(T) is the only sub-Hodge structure with h^{2,0} = 1; its (2,0)-form is symplectic; iota_2(C_1) = 3 pi_0 - pi_12 - pi_13 + 3 pi_23 and cyclically, so the exceptional classes are the twisted dual forms of iota(T); det(x_1 + x_2 + x_3) = Delta(N)^2 and iota(x)^8 = 8! det(x) vol, which with the Fujiki relation rules out hyperkaehler eightfolds |
| `mumford_routes.py` | which of the open routes to the Mumford target are needed: sixteen statements and twenty-two Horn rules, each labelled by the theorem that proves it and checked against paper_labels.txt; the target is not in the closure of what is proved; the statements equivalent to it are exactly algebraicity at uncountably many points, B(W x_C W), bounded data at infinitely many points and bounded data modulo p; every minimal set of open statements yielding it has one element, twelve in all; the complex with dim Ext^2 = 119 and the Kuga-Satake statements are stronger than it; (L) and (V) yield it; it yields neither the Hodge conjecture nor (F1), (F2), (F3); and (F3) is equivalent to the Hodge conjecture, so the target is an input to no minimal route to the conjecture |
| `criterion_shape.py` | what an object meeting the numerical criterion must look like: the rational Weil classes are primitive and the intersection form on the Weil plane is (-1)^n-definite (Gram matrices diag(8d^2, 8d) at n = 2 and diag(-32d^3, -32d^2) at n = 3), so chi(E,E) > 0 by Hodge-Riemann; the Hodge classes killed by P ^ Q are exactly the Weil line in every degree, so an indecomposable summand carries the class; the top traces c_P, c_Q are nonzero; and at n = 2, and at n = 3 granting the degree-three compatibility that the paper's corollary on the Hochschild action already grants, the Euler characteristic forces dim End(E) >= 2 + chi/2 >= 3, with the smallest admissible profiles listed, while at n = 4, 5 it does not |
| `weil_tori.py` | the Hodge classes of a very general Weil torus, the input of the theorem that no complex whose Chern character is exactly a Weil class is semiregular: the Weil classes stay of type (n,n) on the whole 2n^2-dimensional K-linear family; at explicit members off the polarised family no rational class of degree 2k, 0 < k < n, is of Hodge type and in degree 2n only the Weil plane is (checked for n = 2 with d = 1, 3 and for n = 3 with d = 2, ranks modulo a prime with both conjugate conditions imposed); and a Kaehler form in V_+ (x) V_- has zero degree against every Weil class |
| `p2prime.py` | the corrected criterion (P2') as a number: for a Chern character N omega + sum c_k theta^k the annihilator in HT^2 has dimension n^2(4 - rho), rho the rank of the Hankel matrix of the k! c_k, so dim Ext^2(E,E) >= (4 + rho) n^2 - 2n with equality forcing injective semiregularity; for a general shape the annihilator is exactly the tangent space of the polarised Weil family; the n = 2 formula with its two exceptional ratios; the first-order Hodge locus; chi(E,E); at the exceptional n = 2 ratio, the stabiliser so(4,3) of the character (dimension 21, trace-form signature (12,9), invariants 1, 0, 0, 0, 1, 0, 0, 0, 1) and the constant sign of int gamma kappa^2 on the Kaehler cone; exact over Q(i) by torus-weight blocks, to n = 4 by default and n = 9 with --extreme |
| `p2prime_profile.py` | the whole Hochschild profile of such a character: the ranks of contraction on every HT^k equal 2 binom(2n,k) + M_k min(k+1, 2n+1-k, r) - [k=n] d, their symmetry, the middle degeneracy, and the parity of chi(E,E), which makes the numerical criterion unattainable at the n = 2 points with rho_2 = 23 |
| `descent.py` | descent and scalar extension for Weil classes: the correspondence pr_{B*}(x . pr_Y^*(eta_Y^{2m-2} y')) maps the Weil classes of B x Y onto those of B, so W(F,n+1,delta'') gives W(F,n,delta) for every discriminant; and W(F,n,iota(delta)) gives W(K,n,delta) for K in F; exact over seven CM fields |
| `attack_checks.py` | item (LV): a fast subset (about two and a half minutes) of the attack scripts in `attack/`, each track with its verifier's independent re-implementation: the Hodge classes and the criterion numbers of a quartic CM family at n = 2 (2 and 7 Hodge classes, phi^2 = (det H)^{-1}, r = 120, 80, 112 and the bound 68); pull-backs and one composite of correspondences on powers of a Mumford fourfold (7 of 8, then 8); the Hochschild profiles, the n = 2 certificate and the S^2 parity numbers of explicit objects at a split member, and the erratum to the n = 3 example; the natural objects at n = 4 (dim T = 16, rank 6, the relation giving 14 W_2, the lattice index 2612736000); and the gaps of part (E), among them the arithmetic of the sheaves on divisors in the Orlov template (`gaps/orlov_growth/divisor_sheaves.py`: room for n >= 5, ch(G) = r i^*(S T_b), the Ext groups of i_*(V|_Theta), the endomorphisms at n = 5); needs python-flint, sympy and numpy |
| `sextic_count.py` | item (LVI): the dimension count for Orlov products over a sextic CM field: the contraction ranks r^1 = 12, r^2 = 4(A_12+A_13+A_23) + rho_1+rho_2+rho_3 and r^3 = 8 N_w + 2 sum (rk M_+ + rk M_-) into a secant class, exactly over Q(i) and modulo a prime for three cubic fields; the Euler form -64 Nm(q) sum |w|^2 on the secant space, and +16 Nm(q) sum |w|^2 for two places; the profile (1, 12, r^2, e_3, r^2, 12, 1) of a minimal object with e_3 = 2 r^2 - 22 - chi and the bound chi <= -(r^3 - 2 r^2 + 22); standard library only |
| `sextic_lattice.py` | item (LVII): integral flat characters in degree six: chi(v, v) is even on a sixfold, r^3 - 2 r^2 <= 4 for every shape of a secant class (so the profile threshold of Proposition 19.27 is at most 26), and for sixteen totally real cubic fields and q in {1, k + alpha} the lattice of integral points of S(0,q), computed modulo split primes with rational reconstruction, has -chi >= 32, with -chi = 32 exactly at the real and imaginary parts of exp(i theta) when q = 1; the model and the lattice code are in `attack/gaps/sextic/s2_lattice.py`; standard library only |
| `sextic_weil.py` | item (LVIII): the F-Weil part of the twisted character of an Orlov product over a sextic CM field, in closed form (Lemma 19.31), and for the sixteen cubic fields of item (LVII) and q in {1, k + alpha, k + 1 + alpha} the least -chi of an integral flat secant character whose Orlov square has a nonzero F-Weil part: 192, attained only at +-v(-1, 0, 2 - alpha^2, 0) over Q(zeta_7)^+ with q = 3 + alpha; the lattice code is in `attack/gaps/sextic/s3_weil.py`; standard library only |
| `quartic_kernels.py` | item (LIX): kernels on X x X for a quartic CM field at n = 2: a kernel that is not an external product and gives a flat character with a Weil part, the exclusion of kernels supported on graphs and of pure spinors, the shape of the characters of the secant Orlov products, and the arithmetic of Orlov products with negative Ext groups; the one-place model is in `attack/gaps/quartic_kernels/` |
| `mumford_motivic.py` | item (LX): the four possible motivic groups G, G.A_3, N and Sp of a Mumford fourfold, with the dimensions 8, 4, 4, 3 and 125, 45, 35, 15 of the invariants on X^4 and X^6 from the non-crossing pairings, and the formal obstruction: the classes generated by divisor classes, Weil classes, the Hodge classes of the abelian varieties without isogeny factor X and the zeta-fixed classes of the powers of X are all fixed by zeta, and the exceptional classes are not |
| `k3_hodge.py` | item (LXI): Hodge classes on the powers and Hilbert schemes of a K3 surface and on varieties of K3^[n] type: Betti numbers of S^[2], the Fujiki pairing on Sym^2 H^2, the threshold t(t+1)/2 for S^[n] (231 at t = 21), and the fields of the Fano varieties of lines of cubic fourfolds |
| `f3prime_chow.py` | item (LXII): the Hodge numbers behind the reach of the zero-cycle arguments for (F3'): Jacobian rings of smooth hypersurfaces, the primitive Hodge numbers (1, 426, 1751, 426, 1) of a sextic fourfold, the Euler numbers, and the degrees in which a blow-up or a uniruled fivefold needs a class in degree four on a fourfold |
| `mumford_mass.py` | item (LXIII): the Wirtinger bound on a Mumford square in the split model: theta^4 = 24 vol on X and theta_Y^8 = 8! vol on the square, the primitivity of U_12, U_13, U_23, the pairings int pi_ij theta_Y^6 = 0 and int pi_0 theta_Y^6 = 2880, so L(omega_a) = 4 a_0, and L(theta_Y^2) = 56 |
| `cm_source.py` | item (LXIV): the Weil structure of a Mumford fourfold at a CM point and the cycles on its square: the tetrahedra T_+ and T_- = -T_+, 132 = 100 + 32 Hodge classes of degree four, pull-backs of the Weil line along homomorphisms with components in the CM field spanning 110 with the divisor products and no exceptional class, Rosati-symmetric pairs spanning all 132, and the coefficient profile of an exceptional class |
| `quartic_rank.py` | item (LXV): the exact rank of contraction into omega + p(theta_1, theta_2) at a quartic CM field: 34 weight spaces of a six-dimensional torus, r = 64 + 16 mu + 4 rho_1 + 4 rho_2 + R_1 + R_2 with R_t in {7, 8}, the exceptional loci V_+ and V_- by Groebner bases over Q, the fifteen values 80 to 112 (never 100, least 80 only for constant p), the Kaehler class integrals on the Weil tori of the field, and the Hodge locus of every character: first order deformations, exceptional places, the stabiliser so(4,3) and the sign of int X kappa^6; sympy |
| `delsarte.py` | item (LXVI): Delsarte fourfolds: the 29 sextic shapes built from Fermat terms, chains and loops, their Fermat covers (A adj(A) = det(A) I, rows of adj(A) summing to det(A)/6, the least covering degree 24 or 30 for six shapes), smoothness by Groebner bases, and the Jacobian ring (1, 426, 1751, 426, 1) of the loop sextic; sympy and numpy |
| `simplex_type.py` | item (LXVII): hypersurfaces of simplex type: the lattice degree e of the 29 Delsarte sextic shapes by the Smith normal form (e = least d except 3125 for the chain C6 and 2604 for the loop), the Klein quartic (e = 7, the Fermat septic), the Euler numbers of 197 Delsarte hypersurfaces as sums over the orbits of P^{r+1}, the holomorphic forms of top degree as invariant characters of the Fermat cover for 119 hypersurfaces and 40 cyclic covers, nondegeneracy of random polynomials of simplex type, and the smooth adapted fan of the Klein quartic; sympy |
| `quartic_local.py` | item (LXVIII): Markman's candidate for a quartic CM field against the weakened criterion: the classes alpha_0 = Theta - (q/6) Theta^3 and beta' = g^* Theta - (q/6) (g^{-1})^* Theta^3 in the secant space S(0,q), their pure spinor coefficients, the compensated classes x_j = ((q/2) pi_j _| theta_j^2, 0, pi_j) and their B-field transports, the annihilators of dimension 16 and 8 and the ranks 12 and 20, int alpha_0 beta' = -4q Tr(f^2), the Euler pairings, the rank 96 on X x X modulo two primes, and the character Theta - (d/6) Theta^3 and chi = 8d of the first factor; exact rational arithmetic |
| `lattice_congruence.py` | item (LXIX): the secant plane and the lattice of line bundles on a principally polarised abelian fourfold: binomial moments of a class in Q[Theta]/(Theta^5) against the closed formula, u + 3v in the lattice spanned by the e^{j Theta} exactly for d = 15, 23 mod 24 (d < 400, and a second decision by the Vandermonde basis for d < 60), the witness 6(u + v) at d = 3, the defect of m_4 at the smooth discriminants 1, 3, 5, 7, the non-integral moments of O_S for N = 5 to 8, and e(S) != [S]^2 for N <= 40; exact rational arithmetic |
| `burch_rank.py` | item (LXX): resolutions 0 -> E_1 -> E_0 -> I_Z -> 0 by vector bundles of ranks r, r + 1 of a secant ideal I_Z(b Theta): c(I_Z(b Theta)) = 1 + b T + N T^2 + (bN/3) T^3 + N(b^2 - 3d)/12 T^4 by Newton's identities, hard Lefschetz for T^2 on H^2 (rank 28), c_4(G) = -(b^2 + d)(b^2 + 9d)/72 T^4 != 0 at r = 1 (no zero locus of a section of a rank two bundle), 6m = 3d - b^2 - 4ab and chi(E) = a^4 - 2a^2 m + m^2/2 at r = 2, so d = 3 mod 4 at b = 3, confirmed by a brute-force search, and the route note's rank two example (c_4(G) = 180, 144, 84, 0 at d = 1, 3, 5, 7); sympy and exact rational arithmetic |
| `line_bundle_convolutions.py` | item (LXXI): convolutions of line bundles on E^{2n}, E = C/Z[i]: the 2 4^{n-1} bundles L_zeta with prod zeta = +-1, whose signed exponentials sum to the pure Weil class 2 4^{n-1} (alpha + conj alpha), exactly for n = 2, 3; the index lemma n(X + Y) <= n(X) + n(Y); every closed walk of steps of degree one has positive excess at n = 3, 4, so no Massey product enters the diagonal classes of Ext^2, while one of excess 0 exists at n = 2; the degree drop on binary trees; the cup products on the 525 diagonal classes at n = 3 (graph components 4 and 16, generic rank 276, kernel 204 + 45 = 249); among the products of length at least three only the fourfold paths M_{t2} -> M_{t3} -> L -> M_{t1} survive, for sigma_1 = sigma_3 = -sigma_2, with values in a space of dimension (t_2 - t_1)^6, and with t_1 below p and t_2, t_3 above only M_{t2} -> M_{t3} -> M_{t1} -> L and M_{t3} -> M_{t1} -> L -> M_{t2}, for sigma_1 = sigma_2 = -sigma_3; at n = 4 paths of length three and four survive |
| `fourfold_products.py` | item (LXXII): the fourfold products of the surviving family on E_0^6 computed in theta functions: the pieces pulled back along the degree-4 covers (w_1, w_2) -> (w_1 + w_2, u(w_1 - w_2)) of each factor E_0^2, where they become exterior products of line bundles on curves; the automorphy factors, holomorphy and Landau-level norms of the theta functions for d = 2, 6, 14; the selection rules on the two curves; only the tree (x_1 x_2)(y x_3) of the five survives; the explicit convolution M_{t2} -> M_{t3} -> L_zeta -> M_{t1} whose Maurer-Cartan equation is exactly x_1 x_2^zeta = 0 and sum_zeta x_2^zeta x_3^zeta = 0, with 908979, 233213, 12142 classes in degrees 1, 2, 3 of its endomorphism complex; rank 12 at each of the 16 pieces and rank 192 on the 192 diagonal classes of type (1,1,0) (smallest to largest singular value about 0.02, for t = (2,5,6), (2,5,7), both signs, and with the Maurer-Cartan equation imposed), so the diagonal count of the corrected criterion can be met; the partner counts 3, 6, 7 of a piece and the dimensions Prod |zeta_j - zeta'_j|^2 (16 six times and 64 once) of the blocks between pieces of opposite parity that differ in every coordinate; the 112 isolated blocks and 2560 classes of the explicit convolution; random arrangements of the three placements in which every such block with shifts differing by one is isolated; and the bound 249 - (45 + 15 * 9) = 69 > 57 of the theorem that no convolution of these pieces meets the criterion. Double precision |
| `fourfold_certified.py` | item (LXXII), part (H): the rank of the fourfold products proved in ball arithmetic (Arb at 128 bits): every integral of theta functions reduced to coefficients of holomorphic sections by (nabla a) b = (d_a nabla(ab) + H)/(d_a + d_b) with H holomorphic, the coefficients found by interpolation at rational points with the tails of the theta series bounded, the invariant sections on B_j the image of the projector of the two half periods (commuting involutions, checked in rational arithmetic), the theta basis of B_j pulled back by interpolation; agreement with the quadrature to 1e-14; Gram determinants of the 12 columns at each L_zeta and of all 192 columns intervals excluding 0, at t = (2,5,6), with x1 x2 = x2 x3 = 0 (kernels 11 and 19 certified), with the sign reversed and at t = (2,5,7) |
| `diagonal_ci.py` | item (LXXIII): diagonal complete intersections of Vandermonde type, X = {sum_i w_i lambda_i^k x_i^d = 0, k < c} in P^N: the Lagrange identity sum_i w_i f(lambda_i) = 0 for deg f <= N - 1 and the spaces Lambda_r of values of polynomials of degree <= r, exactly; the c x c minors of 957 matrices of Vandermonde type, and 40 pairs of diagonal equations brought to Vandermonde form; in double precision, the map Phi : C^r -> X from the generalised Fermat curve, smooth points of X and fibres of exactly |G| = r! d^{N(r-1)} points; the genus of C three ways, the Euler number of X against the orbifold Euler number of C^r/G in 23 cases, the middle Hodge numbers by Hirzebruch's formula against the sum over characters for 43 triples (d, N, r), dim B_[a] <= 5 for d = 3, 4, 6, N <= 6 and d = 2, N <= 12, and the 70, 490, 6125 balanced orbits of Weil type in P^6 with h^{2,2} = 267, 2584, 48588 |
| `convolutions_efour.py` | item (LXXIV): convolutions of the 128 Weil pieces L_zeta on E_0^8 with three multiples: 4, 12, 28, 20 partners of the other parity differing in 1, 2, 3, 4 coordinates, the 28 with D = 16 or 64 and 640 classes, 64 * 640 = 40960 > 104; no H^0 between distinct pieces and H^1 only across one coordinate; the 1020 runs through the multiples lowering the shift by at least 4; every chain of components the degrees allow at the 1792 pairs of the two-shift theorem, for four placements and both signs, with no element of degree one reaching the classes and no term of d_E leaving them; terms on 6 of 28 groups once a piece moves to a third shift; at three consecutive shifts, 18, 24, 21 partners of the same parity with groups H^5 adding up to 960 per piece, every term the degrees allow landing in H^5 between the highest and the lowest shift (by types for every split, and piece by piece), and the Cayley graph of the targets with least eigenvalue -192, so a cut weighs at most 18432 (attained) and dim Ext^2 >= 22528 |
| `very_general.py` | item (LXXV): the very general diagonal complete intersections of Vandermonde type: the Lie algebra generated by the logarithms N_k = <., c_k> c_k of a chain of vanishing cycles has dimension g(2g + 1), that of sp, for g <= 7; the intersection matrices of the chains, with determinant 1 at even length, for g <= 12; the invariants of sp and sl in the exterior powers (only the powers of the symplectic form, and only the top power); the relations between the signature of a trielliptic curve and its exponents compared with the theorem of Achter and Pries; the determinant formula for the trace form of a hermitian lattice over Z[zeta_3] on 24 random lattices; the dimensions of the space of Hodge classes of the very general member by enumeration of the characters against the closed formulas, 1 + sum_{j > r/2} C(N+1, 2j) for d = 2 and 1 + C(N+1, r+2) C(r+2, r/2+1) for d = 3, never above h^{r/2,r/2} and equal to it for a hypersurface and for two quadrics |
| `cyclic_monodromy.py` | item (LXXVI): the monodromy of the cyclic covers y^m = prod (t - lambda_i)^{a_i} of the line for m = 3, 4, 6, in exact arithmetic over Q(zeta_m): the model of the eigenspace as ker(d)/K l with pure braids acting by Fox Jacobians, its pseudo-reflections and its invariant hermitian form of signature {p, q}; the 38 base cases with n = 3, 4, where the logarithms of the unipotent twists generate sl_n; the collision of two branch points (61 cases), the merge lemma (57213 multisets) and the discriminant of the new part (2 is a norm from Q(i), not from Q(sqrt(-3))); the counts of Hodge classes of the very general member for d = 4, 6 against h^{r/2,r/2} |
| `efour_blocks.py` | item (LXXVII): groups that no product touches on E_0^8: the 13 ratios of one parity that move every coordinate, one of them by -1 (D = 256 once and 64 twelve times, 1024 in all), whose groups H^4 at spread two are reached by no coboundary and left by no term, by an enumeration over the ratios with the degrees on the four surfaces and the degree drop (the 8 ratios with entries +-i are reached and left); nothing leaves a group of spread three; at spread one every term leaving a group H^3 has chains of drop one or two; the runs through the multiples never act at spread 1, 2, 3; every proper subgroup H of the 64 ratios has |H| w(S - H) >= 1024 and the least cut is 1024 (Stoer-Wagner, 129 subgroups); random splits of one parity between two values; piece by piece, the spread-three arrangement (68608 classes, reached only through the loops) and four gap arrangements; every arrangement within five consecutive values excluded, two left within six; the cup products at n = 4 with general components: rank 3184 on the 3584 classes of the L_zeta, kernel 400 + 84 = 484 |
| `efour_six.py` | item (LXXVIII): the diagonal at a lonely shift on E_0^8: a run from a piece through distinct multiples to a piece lowers the shift by 4, 5, 6, 12, 13 or 20, never by 7; with the parities at single shifts s and s - g, g = 5, ..., 13, every term on a diagonal class that the degrees allow runs through the three multiples and no other piece, with shifts pairwise incongruent mod 4, never serving both shifts (320 patterns), so the 1792 diagonal classes at one shift survive; the 28 ratios that move three coordinates and change the parity weigh 640 and every proper subgroup H of the 128 ratios has |H| w(S_3 - H) >= 640 (636 subgroups, least cut 640 by Stoer-Wagner); random interleaved splits {s, s-4}, {s-1, s-5} piece by piece, whose groups H^3 are reached by nothing and left by nothing; every arrangement within six consecutive values excluded |
| `transport_growth.py` | the transport of the base cycle along the rational orbit: det(phi) = c^{2G}, phi^* E = c^2 E and phi^* omega = c^{2n} omega on an explicit sample of rational symplectic elements with denominators to 29; the multiplicity of a component as the order of the stabiliser its kernel meets, computed as a lattice index by Smith normal form, against the image degree computed as a Pfaffian; and the contrast between a subtorus the isogeny preserves, where the image degree is constant, and one it does not, where it grows |
| `cm_fields.py` | the Weil classes of a CM field of degree four and six: the CM base point of every family, the balanced divisor classes delta_i(f), the identity that the balanced n-fold product of them is the Weil class w(f) = sum_sigma sigma(f) alpha_sigma, checked for six pairs (F, n) with m = 2, 3 and n = 1, 2, 3, and the identity that the Weil classes of a composite field generate those of its imaginary quadratic subfield |
| `exceptional_classes.py` | the exceptional Hodge classes on the self-product of a Mumford fourfold (eight invariants against six divisor products), the Hodge numbers and adjoint weights that keep the H^3 of a quintic threefold outside abelian type, and the 4n^2-dimensional annihilator of the Weil class in Hochschild cohomology with the two linear-algebra lemmas behind the theorem on the semiregularity form of propagation |
| `mumford_rm.py` | the two exceptional classes on the self-product of a Mumford fourfold as a real multiplication: the commutant of sl(2)^3 on wedge^2 V (four isotypic projectors, ranks 1, 9, 9, 9), the Hodge numbers of the pieces and the K3 type (1,7,1) of the Lie algebra, the product map mu from T (x) T onto H^2(X), the scalar nu by which mu mu^dagger acts on the primitive part U, the transport formula nu g_i g_j with g = e^2/lambda, the norm form 4e^2/lambda of the Kuga-Satake map, and the Kuga-Satake map on the explicit Clifford algebra C(T): C^+(T) = V (x) W with dim W = 32, Psi(v) = v (x) N_i on T_i, and the three N_i anticommuting and independent, which forces the entries of the map to span the cubic field |
| `split_resolution.py` | the data behind the theorem that no two-term complex of powers of the polarisation runs the weakened criterion: the nonzero scalar on a line bundle, the vanishing of H^2 of nontrivial powers on an n-fold with n >= 3, the minimality and secant moments of the three split resolutions found by `hilbert_burch.py`, and the complete-intersection control |
| `paper_labels.txt` | every `\label` of the paper sources, generated from them; `closure_graph.py` checks each theorem label it names against this list |
| `pte_remaining.py` | the three level sets at n = 3 left open by `pte_search.py`, settled by a complete vectorised search (needs numpy) |
| `quaternionic_divisibility.py` | the quaternionic Weil cycle on the lattice O_b^2: it is b^2 times a fixed integral cycle, and the polarisation degree grows like b^2 |
| `divisor_route.py` | the divisor route at n = 2 on one fixed polarised lattice: the K-bilinear classes, the trace identity for the Hodge norm, a pencil of quaternionic loci, and the growth of the least divisor norm along it |
| `split_obstruction.py` | the first-order obstruction map of a split object against the tangent space of the Weil family: kernel the tangent space of the split locus, rank n(n-1)/2, image inside the kernel of the semiregularity map and transverse to the copy of the tangent space there |
| `evaluation_map.py` | the evaluation map of Hochschild cohomology on the explicit split object, in the Hodge basis: the commutative square with the semiregularity map, the rank of the map, and the fact that the whole kernel of the semiregularity map lies in its image, for the explicit object and for every configuration in the box |
| `markman_candidate.py` | the Chern character of Markman's candidate object in dimension eight, exactly: it sits at the point (1,3) of the secant plane for the twist by 3 Theta, the Euler characteristic of the partially normalised union is (d+9)(27-d), and the transforms have nonzero rank |
| `secant_kernel.py` | the Hochschild classes preserving a secant Chern character a u_t + b v_t on an abelian n-fold, n = 3, 4, 5: none in HT^1, and in HT^2 exactly the polarised deformations and the Poisson classes compensated by (d/2) pi _| t^2, n^2 in all, with the controls that the bare and the wrongly compensated classes fail; and the B-field identity x _| (w e^B) = ((e^B x) _| w) e^B |

All arithmetic is exact: `fractions.Fraction`, Python integers, exterior
algebra over the rationals with integer structure constants, or, in
`weil_tangent.py`, the Gaussian rationals built from `fractions.Fraction`.
No step converts to a float, except in `fourfold_products.py` and in parts
(C) and (D) of `diagonal_ci.py`, which test a map proved by hand on random
points; no statement of the paper rests on those two parts. Two scripts, `semireg_fast.py` and
`weil_annihilator.py`, also work modulo a prime, where full rank is a
certificate of full rank in characteristic zero; `weil_tangent.py` uses no
reduction at all.

## Running the Lean check

    cd lean
    elan toolchain install $(cat lean-toolchain)
    lake build
    lean HodgeObstruction.lean

No Mathlib and no dependencies. The file ends with one `#print axioms` line
per theorem; every one must read `does not depend on any axioms`, or
`depends on axioms: [propext]` where propositional extensionality enters
through `decide`, and none may mention `sorryAx`. There are four hundred and nine theorems. `lean/README.md` lists them
and says what each one does and does not establish. The workflow in
`.github/workflows/lean.yml` runs the check on every push and fails if the
number of theorems is not four hundred and nine, or if any of them depends on an axiom other than propext.

## The computations, item by item

`COMPUTATIONS.md` describes the computations as items (I) to (LXXVIII) and lists,
for each result of the paper, the items that check it. The programs that carry
them out are:

| item | program |
| --- | --- |
| (I) | `code/verify_all.py` (built in) |
| (II) | `code/verify_all.py` (built in) |
| (III) | `code/verify_all.py` (built in) |
| (IV) | `code/verify_all.py` (built in) |
| (V) | `code/verify_all.py` (built in) |
| (VI) | `code/explicit_weil.py` |
| (VII) | `code/hodge_invariants.py` |
| (VIII) | `code/kugasatake.py` |
| (IX) | `code/weiltype_family.py`, `code/secant_plane.py` |
| (X) | `code/split_locus.py` |
| (XI) | `code/split_geometry.py` |
| (XII) | `code/quaternionic.py` |
| (XIII) | `code/semiregularity.py`, `code/semireg_fast.py` |
| (XIV) | `code/weil_annihilator.py` |
| (XV) | `code/weil_product.py` |
| (XVI) | `code/weil_tangent.py` |
| (XVII) | `code/lagrangian_locus.py` |
| (XVIII) | `code/object_size.py` |
| (XIX) | `code/rigidity.py` |
| (XX) | `code/integrality.py` |
| (XXI) | `code/secant_exists.py` |
| (XXII) | `code/pte_search.py`, `code/pte_remaining.py` |
| (XXIII) | `code/quaternionic_divisibility.py` |
| (XXIV) | `code/divisor_route.py` |
| (XXV) | `code/split_obstruction.py` |
| (XXVI) | `code/evaluation_map.py` |
| (XXVII) | `code/markman_candidate.py` |
| (XXVIII) | `code/secant_kernel.py` |
| (XXIX) | `m2/local_products.m2` |
| (XXX) | `code/smooth_support.py` |
| (XXXI) | `m2/lci_products.m2` |
| (XXXII) | `code/hilbert_burch.py` |
| (XXXIII) | `code/closure_graph.py` |
| (XXXIV) | `code/split_resolution.py` |
| (XXXV) | `code/exceptional_classes.py` |
| (XXXVI) | `code/cm_fields.py` |
| (XXXVII) | `code/transport_growth.py` |
| (XXXVIII) | `code/hochschild_annihilator.py` |
| (XXXIX) | `code/p2_support.py` |
| (XL) | `m2/finite_length_products.m2` |
| (XLI) | `code/mumford_rm.py` |
| (XLII) | `code/lefschetz_family.py` |
| (XLIII) | `code/targets_reduction.py` |
| (XLIV) | `code/mumford_rigidity.py` |
| (XLV) | `code/mumford_object.py` |
| (XLVI) | `code/lefschetz_closure.py` |
| (XLVII) | `code/twistor_locus.py` |
| (XLVIII) | `code/hk_pullback.py` |
| (XLIX) | `code/mumford_routes.py` |
| (L) | `code/criterion_shape.py` |
| (LI) | `code/weil_tori.py` |
| (LII) | `code/p2prime.py` |
| (LIII) | `code/p2prime_profile.py` |
| (LIV) | `code/descent.py` |
| (LV) | `code/attack_checks.py` |
| (LVI) | `code/sextic_count.py` |
| (LVII) | `code/sextic_lattice.py` |
| (LVIII) | `code/sextic_weil.py` |
| (LIX) | `code/quartic_kernels.py` |
| (LX) | `code/mumford_motivic.py` |
| (LXI) | `code/k3_hodge.py` |
| (LXII) | `code/f3prime_chow.py` |
| (LXIII) | `code/mumford_mass.py` |
| (LXIV) | `code/cm_source.py` |
| (LXV) | `code/quartic_rank.py` |
| (LXVI) | `code/delsarte.py` |
| (LXVII) | `code/simplex_type.py` |
| (LXVIII) | `code/quartic_local.py`, with `m2/local_germs.m2` for the local part |
| (LXIX) | `code/lattice_congruence.py` |
| (LXX) | `code/burch_rank.py` |
| (LXXI) | `code/line_bundle_convolutions.py` |
| (LXXII) | `code/fourfold_products.py`, with `code/fourfold_certified.py` for part (H) |
| (LXXIII) | `code/diagonal_ci.py` |
| (LXXIV) | `code/convolutions_efour.py` |
| (LXXV) | `code/very_general.py` |
| (LXXVI) | `code/cyclic_monodromy.py` |
| (LXXVII) | `code/efour_blocks.py` |
| (LXXVIII) | `code/efour_six.py` |

Items (I) to (V) are computed inside `code/verify_all.py` itself; items
(XXIX), (XXXI) and (XL) are the Macaulay2 computations described below; item
(LV) runs a fast subset of the programs in `code/attack/`, whose README states
each of their results with its status.

## The Macaulay2 items

Four items of the paper are Ext computations over a polynomial ring and are
carried out in Macaulay2 1.22 with the package `Complexes`:

| script | item | what it settles |
| --- | --- | --- |
| `m2/local_products.m2` | (XXIX) | the local Ext modules and the products of the translation classes at an isolated double point of the support of Markman's candidate, in both local models |
| `m2/lci_products.m2` | (XXXI) | that the local obstruction lives exactly at the germs that are not Cohen-Macaulay: Ext^2(I,I) vanishes at seven Cohen-Macaulay germs, two of them not complete intersections, and not at three that are not Cohen-Macaulay |
| `m2/finite_length_products.m2` | (XL) | that two independent jet classes on a complex with finite length cohomology multiply to a nonzero class whenever its Euler characteristic is nonzero, on eighteen modules and three complexes in two and three variables, and that the hypothesis is sharp: on the cone of the product on the Koszul complex of a point the product vanishes |
| `m2/local_germs.m2` | (LXVIII) | for ten germs in C^4, the projective dimension and the pairs of coordinate directions whose jet classes have nonzero Yoneda product in the local Ext^2: the second exterior power of the normal space for a bundle on a smooth curve, exactly {1} x {2,3} for the ideal of a curve in a divisor, none for a smooth divisor or a maximal Cohen-Macaulay module on a node; the local part of the theorem that Markman's quartic candidate fails the weakened criterion |

Each runs in under a minute:

    cd m2
    M2 --script local_products.m2
    M2 --script lci_products.m2
    M2 --script finite_length_products.m2
    M2 --script local_germs.m2

Their unedited transcripts are the `.txt` files beside them, and
`m2/README.md` says what each line means. They are not part of
`verify_all.py`.

## Rebuilding the figures

    cd figures
    python3 make_core.py        # the Weil cube, the Hodge spike, the character
                                # grid, the Chern line, the annihilator, the
                                # witnesses of the two characters
    python3 make_plates.py      # the quadric, the Lagrangian sweep, the fibres
    python3 make_secant.py      # the moment curve, the secant plane and the
                                # least multiple M
    python3 make_smooth.py      # the Bogomolov-Miyaoka-Yau window
    python3 make_more.py        # the hypothesis cube and the null cone
    python3 make_properness.py  # the closed strata of the algebraic locus
    python3 make_diagrams.py    # the Lefschetz ladder, the moduli count, the
                                # signature surface
    python3 make_closure.py     # the closure graph
    python3 make_support.py     # the support theorem
    python3 make_mumford.py     # a Mumford fourfold and its K3 surface
    python3 make_frontier.py    # the five minimal sufficient sets as ribbons,
                                # propagation along a compact Shimura curve,
                                # the Leray summands of an abelian scheme over
                                # a curve with the four operators of the proof,
                                # the rigidity of the Mumford classes, the
                                # audit of the bypass mechanisms, and the
                                # self-extension bounds for the Mumford object
    python3 make_round11.py     # the web of Weil families under descent,
                                # the corrected criterion as a number, and
                                # the Kaehler sign at the exceptional ratio
    python3 make_round12.py     # minimal support at n = 4, and the loci
                                # where quartic CM Weil classes are known
                                # to be algebraic
    python3 make_round19.py     # the sextic Weil part, the motivic groups of
                                # a Mumford fourfold, the reach of (F3'), the
                                # K3 threshold
    python3 make_round20.py     # the CM cube, the CM source, the mass gap
    python3 make_round21.py     # the quartic rank, the Delsarte shapes
    python3 make_round22.py     # hypersurfaces of simplex type
    python3 make_round24.py     # the local obstruction at a point of
                                # Markman's glued curve, and the ten germs
    python3 make_round28.py     # the algebraic locus of the main theorem,
                                # and the two halves of the closure theorem
    python3 make_round31.py     # an abelian scheme seeded at a CM member
    python3 make_round32.py     # the excess of a cycle of line bundles, the
                                # surviving fourfold path, and the budget of
                                # diagonal classes at n = 3
    python3 make_round37.py     # the special locus and the escaping sequence
    python3 make_round40.py     # diagonal complete intersections of
                                # Vandermonde type, two shifts on E_0^8
                                # (with the strip of three shifts)
    python3 make_round41.py     # the monodromy of the curves D_a, the very
                                # general complete intersections by degree
                                # and dimension, their Hodge classes against
                                # h^{r/2,r/2}, and the map of the paper
    python3 make_round42.py     # the monodromy of cyclic covers: collision,
                                # two copies of SL(Y), induction on n
    python3 make_round43.py     # three consecutive shifts on E_0^8: blocks,
                                # targets, budget and spectrum
    python3 make_round44.py     # groups of spread two, the arrangements
                                # within five values, the diagonal at n = 4
    python3 make_round45.py     # the diagonal at a lonely shift,
                                # interleaved shifts, six values
    for f in fig_*.tex; do pdflatex -interaction=nonstopmode "$f"; done
    python3 checkfigs.py        # must print 0 overlapping label pairs

Six figures, `fig_doublepoint`, `fig_evaluation`, `fig_factor`,
`fig_pencil`, `fig_product` and `fig_tangent`, are block diagrams written
directly in TikZ; their `.tex` files are the sources.

`render3d.py` is a small painter's-algorithm renderer with a perspective
camera and Lambert shading that emits TikZ; the `make_*.py` scripts pass it
their own surfaces, curves, solids and labels. Its constant `DETAIL`, set to
1.5, multiplies every mesh and every sampled curve. `place.py` puts every label
outside the ink rectangle of its own figure and draws a leader to it, and
`checkfigs.py` re-reads the emitted TikZ of every figure and reports any pair
of label boxes that touch; it currently reports none. `palette.tex` holds the
shared colours.

## What is and is not claimed

The theorems of the paper are statements of algebraic geometry and are not
formalised. What is checked here is the arithmetic on which they turn.

The paper does not prove the Hodge conjecture and does not claim to. The
algebraicity of Weil classes on abelian fourfolds, and hence the Hodge
conjecture for abelian varieties of dimension at most five, is a theorem of
Markman (arXiv:2502.03415, arXiv:2509.23403) and is quoted as prior work.

What the paper proves, in every dimension, is the following. The annihilator
of the Weil line in H^{0,2} is canonically the tangent space to the Weil
family, so no object whose Chern character lies on that line is semiregular,
and the weaker hypothesis of Question 11.4 of arXiv:2509.23403 fails for such
objects as well (`weil_annihilator.py`, `evaluation_map.py`). No sum of line
bundles, at any member and in any dimension, satisfies either criterion
(`split_obstruction.py`, `rigidity.py`). For a secant object the local part
of the weakened criterion is a condition on depth, which removes Markman's
candidate in dimension eight (`markman_candidate.py`, `m2/`), and the
Cohen-Macaulay supports that remain admit no resolution by line bundles or
semi-homogeneous bundles that runs the criterion (`hilbert_burch.py`,
`split_resolution.py`).

On the positive side, every Weil family of every CM field, every dimension
and every discriminant has a base point at which the Weil classes are
polynomials in divisor classes (`quaternionic.py`, `cm_fields.py`), and the
conjecture for the family is the algebraicity of one class on one connected
domain. What separates a base point from the family is one propagation
statement: that at one base point some perfect complex with the Weil Chern
character has injective semiregularity map. The paper shows that this holds
as soon as the complex has Ext^2 of dimension 2n(2n-1), the least the
Hochschild computation allows, and that such a complex cannot be supported in
codimension n, so it cannot be carried by any cycle representing the class
(`hochschild_annihilator.py`, `p2_support.py`,
`m2/finite_length_products.m2`). In that form the statement is false, in every
dimension: a complex whose Chern character is exactly a Weil class and whose
semiregularity map is injective would deform along every K-linear deformation
of the abelian variety, hence to very general non-algebraic Weil tori; on those
the only Hodge classes below the top degree are the Weil classes, there are no
subvarieties but points, and every coherent sheaf has vanishing Chern character
in degrees 1 to 2n-1 (Voisin's theorem in dimension four, and the same
argument through Bando-Siu Hermite-Einstein metrics in every dimension). So no
complex meets the Ext^2 criterion (`weil_tori.py` checks the Hodge-theoretic
input). The statement survives in a corrected form, in which the Chern
character may also carry powers of the polarisation; the propagation theorem
holds for it unchanged, and so does a weaker flatness form of it, which
tolerates an object obstructed to first order. For that form the rank of contraction from HT^2 into
the Chern character is (4 + rho) n^2 - 2n for n >= 3, where rho <= 3 is the
rank of a Hankel matrix of the coefficients of the polynomial, and a complex
whose Ext^2 has exactly that dimension meets the criterion; for a general
polynomial the annihilator is exactly the tangent space of the polarised
family. At n = 2 the rank takes the values 12, 16, 18, 20, 22, 23 and 24, and
23 is excluded by parity. The shapes A e^{t theta} + B theta^{2n}, with
t theta the class of a line bundle, which have rho <= 2, are excluded as the
pure form was; for every other shape and n >= 3 the Hodge locus of the Chern
character is the polarised family itself, so that obstruction does not
extend, and at n = 2 one exceptional ratio gives a five-dimensional locus
whose stabiliser is so(4,3) (`p2prime.py`, `p2prime_profile.py`, exact to n = 9, and to
n = 10 in `code/extreme/`). This is a number an object would have to reach;
nothing here constructs one or decides whether one exists. At a quartic CM
field the rank is at least 80, a complex meeting the criterion has
dim Ext^2 >= 88, and the Hodge locus of each character, computed to first
order, is the family of Weil tori only for the theta^4 shape, which is
therefore excluded, and the polarised family itself for every other character
left at 88, so deformation cannot exclude those (`quartic_rank.py`). Markman's
explicit pair for a biquadratic field does not meet the weakened criterion:
two compensated classes in HT^2, one for each real place, preserve every
quartic secant character, and at a point where a sheaf is locally free on a
smooth curve, or is the ideal of a curve in a smooth divisor, the square of
the Atiyah class along one of the two eigenplanes has a nonzero germ; the
curves Markman glues in to correct the character have such points
(`quartic_local.py`, `m2/local_germs.m2`). Whether another sheaf with the same
character meets the criterion, Markman's Question 11.2.2, stays open.

The Hodge conjecture follows from that statement together with two more, the
algebraicity of the Hodge classes on abelian varieties that divisor and Weil
classes do not generate, and the conjecture for varieties that are not
abelian. The last of these is the conjecture itself: the varieties that are
not abelian include A x P^1 for every abelian variety A, and the conjecture
for A x P^1 gives it for A (pull back along the projection, cup with the
class of A x {0}, push forward), so it alone implies the conjecture for
abelian varieties and then the whole conjecture (Proposition prop:f3ishc of
the paper). The statement that belongs in its place, (F3'), asks for every Hodge
class to be algebraic modulo images of Hodge classes of abelian varieties
under algebraic correspondences. It holds on every variety whose cohomology
is reached from abelian varieties in that way (curves, abelian varieties,
products, surjective images), in degrees 0, 2, 2n-2, 2n, and in dimension at
most three; in degree four it descends along dominant rational maps, which
puts every smooth Delsarte fourfold in its domain, among them 28 sextic
fourfolds besides the Fermat one (Propositions prop:f3primedominant and
prop:delsarte, `delsarte.py`); beyond that it is open, and nothing here
closes it (Proposition prop:f3prime and Remark rem:f3primeopen). With (F3') the three statements are
a minimal route (`closure_graph.py`, and Section 24 of the Lean file).
The second and
third are not reductions: the self-product of a
Mumford fourfold carries two Hodge classes outside the subring of divisor and
Weil classes, and the H^3 of a very general quintic threefold is not of
abelian type (`exceptional_classes.py`). The two classes on the Mumford
fourfold are the real multiplication by a totally real cubic field on the
primitive part of H^2, and they are algebraic once the Kuga-Satake class of
one of the K3 surfaces of Picard number thirteen attached to the fourfold is
algebraic (`mumford_rm.py`). That Kuga-Satake class is
not known to be algebraic.

With the implications of the literature added, the rule set has exactly five
minimal sufficient sets: the conjecture for varieties that are not abelian
alone; the Lefschetz standard conjecture (L) with the motivatedness of every
Hodge class (M), which together are also equivalent to the conjecture; and
(F3') with (L), with the variational Hodge conjecture for algebraic classes
(V), or with the propagation statement and (F2), the route of the paper, which
is the only one that uses anything proved here. Every member except the
propagation statement is a consequence of the conjecture
(`closure_graph.py`, Section 24 of the Lean file). The propagation statement
is needed only for the split families of the CM fields of degree at least
four. A descent lemma (Proposition prop:descent) links the Weil families: the
product B x Y with an abelian surface Y of Weil type, and a push-forward
against the Weil class of Y, carries the Weil classes of a family in dimension
n+1 to those of every family in dimension n, of every discriminant; and
scalar extension from K to a CM field F containing it carries the Weil
classes of F-families to those of K-families (`descent.py`). The consequence is that the secant route, granted every demand it makes,
reaches every imaginary quadratic family and still no CM field of higher
degree, so it remains outside every minimal set. One new case of
(L) is proved: for an abelian scheme over a curve whose invariant cycles are
algebraic, the Lefschetz operator is a relative Pontryagin product with
l^{g-1}/(g-1)! plus an operator along the base built from the invariant
cycles, so it is algebraic; this covers the total space of every Mumford
family (`lefschetz_family.py`, `mumford_invariants` in the Lean file). The
mechanism goes back to Tankeev (Izv. Math. 67 (2003)). With Markman's theorem
it gives the Lefschetz standard conjecture for every abelian scheme over a
curve of relative dimension at most four whose invariant classes are Hodge,
and for every fibre power of a family of Weil fourfolds with connected
monodromy SU(V,H), through the Hodge conjecture for all powers of such a
fourfold, which is known (Milne, arXiv:2112.12815) and is reproved in the
paper from the first fundamental theorem for SL. Over its Shimura curve the
total space of a Mumford family satisfies the Hodge conjecture.
For such a total space (L) is exactly propagation of algebraicity along the
curve, so each remaining target becomes one case of (L): one Weil family is
equivalent to (L) for the total space of the family over a curve through a
base point, and the first classes beyond the Weil lines are equivalent to (L)
for the ninefold W x_C W of a Mumford family. Proved outright on the way: the
Hodge conjecture for X_c x X_c at every CM point of a Mumford family
(`targets_reduction.py`), and that no direct sum of objects with exterior Ext
algebras (line bundles, sheaves on abelian subvarieties, simple
semi-homogeneous bundles, points and their Fourier-Mukai images) meets the
corrected semiregularity criterion, because an object meeting it does so
through one indecomposable summand (Lemma lem:p2primesummands and Corollary
cor:naturalsums; the version for the first form of the criterion,
`two_branch_annihilator` in the Lean file, is vacuous since that form is
false). The Mumford classes are rigid: the only first order deformation of
the square keeping a rational exceptional class of Hodge type is the direction
of the compact Mumford curve, so no degeneration or larger family reaches them;
propagation along the curve follows from one perfect complex at one CM point
with dim Ext^2 = 119, or from a degree bound at infinitely many CM points
(`mumford_rigidity.py`, `mumford_rigidity_sos` in the Lean file). No
construction from line bundles by cones, tensor products, pull-backs,
push-forwards and Fourier-Mukai functors reaches the Mumford classes, at any
point of the curve, because all of these preserve invariance under the
Lefschetz group (`lefschetz_closure.py`, `lefschetz_counts` in the Lean file).
Among all complex tori, algebraic or not, the component of the Hodge locus of
an exceptional class through the square is the Mumford curve itself, so no
twistor line through a member keeps the class of Hodge type and Markman's
twistor transport for Weil classes cannot move it; the twistor lines on which
the class is of Hodge type carry non-algebraic tori (`twistor_locus.py`).
The square is a holomorphic symplectic variety whose symplectic class generates
the structure T of K3 type inside H^1 (x) H^1, and the exceptional classes are
exactly the dual forms of T twisted by the real multiplication; pull-back of
the dual Beauville-Bogomolov class along a rational map onto a symplectic
subvariety of a hyperkaehler manifold of dimension at least ten, such as the
Hilbert scheme of n >= 5 points on a K3 surface of Picard number thirteen,
would prove them algebraic, and no K3 surface or hyperkaehler eightfold can
serve (`hk_pullback.py`). The five routes that are not closed off are one
statement: specialisation, reduction modulo p and the Lefschetz standard
conjecture for W x_C W are the target itself, the complex with dim Ext^2 = 119
and the Kuga-Satake class imply it, and one of them would suffice; the target
is only the first case of (F2), so a proof of it would leave (F1), the other
cases of (F2) and (F3) open, and (F3) is the whole conjecture
(`mumford_routes.py`).
By Li's theorem (arXiv:2609.27916) the classes are represented by algebraic
cycles at every closed point of every reduction of the curve modulo a prime,
and the target is equivalent to a bound on the Hilbert data of those cycles on
a Zariski dense set of closed points of the arithmetic model. No such complex
and no such bound is known.

A complete intersection of diagonal hypersurfaces of one degree d in P^N whose
coefficient columns lie on a rational normal curve, which holds for every
smooth complete intersection of two diagonal hypersurfaces, is the quotient
C^r/G of a power of a generalised Fermat curve C by a finite group, so it
satisfies (F3') in every degree, and its Hodge conjecture is that of the
abelian varieties B_[a] cut out of the Jacobian of C by the characters; it
holds when they have dimension at most five, in particular for two diagonal
cubics, quartics or sextics in P^6, through Markman's theorem
(`diagonal_ci.py`). At a very general configuration the monodromy of the
cyclic covers D_a of the line decides the Hodge classes: for characters of
order two it contains Sp(H^1(D_a)) (chains of vanishing cycles, A'Campo), so
only powers of the polarisation survive; for characters of order three, four
and six its identity component contains SL of the eigenspace, proved by
letting two branch points collide, a lemma on two copies of SL of a
hyperplane, a merge lemma and 38 computed base cases, so only Weil classes
of abelian r-folds of Weil type for Q(sqrt(-3)) or Q(i) survive, of trivial
discriminant except for characters of order six with an odd number of
coordinates 3. Hence the very general member satisfies the Hodge conjecture
for d = 2 in every dimension, for d = 3, 4 up to dimension seven and for
d = 6 up to dimension five, in every P^N; for d = 6 in dimension six the
Hodge classes are algebraic except on non-split Weil sixfolds. The space of
Hodge classes of degree r has dimension 1 + C(N+1, r+2) T_d(r+2), plus
sum_{j > r/2+1} C(N+1, 2j) for d even, for instance 141 for two cubics in
P^6 against h^{2,2} = 267 and 3950 for three quartics in P^7 against 29872
(`very_general.py`, `cyclic_monodromy.py`). These use known cases of (F2)
and are not new cases of it.

The attack scripts (`code/attack/`, item (LV)) examine the inputs the closure
graph leaves open, each with an independent adversarial re-implementation. For a
quartic CM field F at n = 2, the smallest open case of the propagation
statement the minimal route needs, divisor classes reach the Weil classes
exactly on a Noether-Lefschetz locus of the weight-two part R_F, of
codimension two when the discriminant is trivial, governed by the quaternion
algebra (F/F_0, det H^{-1}); for biquadratic F Markman's theorem reaches them
on a locus of dimension four; the Casimir class of R_F is algebraic exactly
when the Weil classes are; correspondences with abelian varieties of
dimension at most seven cannot help at a Hodge-generic member; and the
corrected criterion asks dim Ext^2 = 112 of one complex for a general shape;
the rank it asks for takes fifteen values, the least being 80 and only for a
constant polynomial part, the pure shape is excluded for every CM field, and
so a complex meeting the criterion has dim Ext^2 >= 88. If the two exceptional classes of a Mumford
fourfold X are algebraic on X x X, every Hodge class on every power of X is
(one hyperdeterminant class needs a composite of correspondences); the
Kuga-Satake route asks for that and a link besides, and no link passes
through an abelian variety of dimension at most five. For the imaginary
quadratic families the criterion reduces to one indecomposable object; Orlov
products of explicit secant objects meet its twisted form with equality at
n = 2 and n = 3 and cannot at n = 4; and at n = 4 a combination of natural
objects with a Weil part needs at least eight of them, on one conic of the
quadric of Lagrangians, as in the relation sum m_i [B_i] = 14 W_2 over eight
graph subvarieties. None of this is a new case of the Hodge conjecture: the
unconditional proof still needs the propagation statement for the split
families of the CM fields of degree at least four, the classes beyond the Weil
lines (F2), and the conjecture modulo abelian varieties (F3').

Nothing here is a proof of the Hodge conjecture.

## Licence

The code and figure sources are released under the MIT licence; see `LICENSE`.
