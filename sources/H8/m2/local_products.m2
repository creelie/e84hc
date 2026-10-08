-- local_products.m2
--
-- The local products of the translation Kodaira-Spencer classes at an
-- isolated double point of the support of Markman's candidate.  Item (XXIX).
--
-- Two smooth surfaces P1 = {x1 = x2 = 0} and P2 = {x3 = x4 = 0} meet
-- transversally at the origin of C^4.  The candidate is locally either
--
--   (I)  the ideal sheaf I = I_{P1} cap I_{P2}         (a point not normalised), or
--   (K)  the complex  K = [O --> O_{P1} (+) O_{P2}]     (a normalised point).
--
-- For a module or complex F and a derivation D = d/dx_a, the jet extension
-- 0 -> F -> J_D(F) -> F -> 0 represents the contraction of the Atiyah class
-- with D, the first order deformation of F along the translation flow of D.
-- On a free resolution P of F with differential d it is the degree -1 chain
-- map -D(d), the entrywise derivative of the differential.  The Yoneda
-- product of two such classes is the composite of the two chain maps, and
-- the product vanishes in Ext^2(F,F) exactly when the composite is null
-- homotopic.
--
-- Output: for both models, the dimensions of the local Ext modules, and for
-- every pair (a,b) whether the product a_a * a_b vanishes.  Expected:
--   (I): Ext^2 = k^4; the product vanishes exactly for the pairs with both
--        directions normal to the same plane, {1,2} and {3,4}; the mixed
--        pairs give four independent nonzero classes;
--   (K): Ext^2 = k^2; the product vanishes exactly for the mixed pairs; the
--        pairs {1,2} and {3,4} give two independent nonzero classes.
-- The first case is also recomputed with yonedaProduct on the jet modules.
--
-- Run:  M2 --script local_products.m2      (Macaulay2 1.22, package Complexes)

needsPackage "Complexes";
R = QQ[x1,x2,x3,x4];
I1 = ideal(x1,x2); I2 = ideal(x3,x4);
vars4 = {x1,x2,x3,x4};

-- the degree -1 chain map on a free complex P representing the jet class along d/dx_a,
-- shifted internally by s so that the composites are homogeneous
ksMap = (P, a, s) -> (
   Ps := P ** R^{-s}; Pt := P ** R^{-s-1};
   map(Pt, Ps, i -> map(Pt_(i-1), Ps_i, -diff(R_a, dd^P_i)), Degree => -1));

report = (name, P) -> (
   print("== model " | name | " ==");
   print("free resolution ranks: " | toString apply(toList(min P..max P), i -> rank P_i));
   H := Hom(P, P);
   for i from 1 to 2 do (
      E := prune HH_(-i) H;
      print("Ext^" | toString i | " = " | toString E);
   );
   for a from 0 to 3 do (
      f := ksMap(P, a, 0);
      print("a_" | toString(a+1) | ": anticommutes with d: " | toString isCommutative f
            | ", nonzero class: " | toString (not isNullHomotopic f));
   );
   zeros := {};
   nonzeros := {};
   for a from 0 to 3 do for b from a to 3 do (
      g := (ksMap(P, b, 1)) * (ksMap(P, a, 0));
      if isNullHomotopic g then zeros = append(zeros, (a+1,b+1)) else nonzeros = append(nonzeros, (a+1,b+1));
   );
   print("products a_a * a_b that vanish:    " | toString zeros);
   print("products a_a * a_b that are nonzero: " | toString nonzeros);
   -- anticommutation a_a a_b + a_b a_a = 0 for a < b
   anti := true;
   for a from 0 to 3 do for b from a+1 to 3 do (
      g := (ksMap(P, b, 1)) * (ksMap(P, a, 0)) + (ksMap(P, a, 1)) * (ksMap(P, b, 0));
      anti = anti and isNullHomotopic g;
   );
   print("anticommutation holds: " | toString anti);
);

-- (I) the ideal of the two planes
I = intersect(I1, I2);
MI = coker presentation module I;
PI = freeResolution MI;
report("(I)  I = I_{P1} cap I_{P2}", PI);

-- cross-check of (I) through the jet modules and yonedaProduct
S = presentation MI;
Dmat = (i, A) -> matrix apply(entries A, row -> apply(row, e -> diff(R_i, e)));
jetClass = (i, s) -> (
    DS := Dmat(i, S);
    Ms := MI ** R^{s}; Ss := presentation Ms;
    tgt := R^{4:-2+s} ++ R^{4:-1+s};
    blk := map(tgt, , (Ss | (-DS)) || (map(R^{4:-2+s}, source Ss, 0) | Ss));
    J := coker blk;
    d1 := map(MI ** R^{s+1}, J, (cover J)^[1]);
    d2 := map(J, Ms, (cover J)_[0]);
    C := complex{d1, d2};
    assert isShortExactSequence C;
    yonedaExtension' C);
A0 = apply(4, i -> jetClass(i, 0)); A1 = apply(4, i -> jetClass(i, 1));
yz := {}; ynz := {};
for a from 0 to 3 do for b from a to 3 do (
    h := yonedaProduct(A1#b, A0#a);
    if h == 0 then yz = append(yz, (a+1,b+1)) else ynz = append(ynz, (a+1,b+1));
);
print("cross-check with yonedaProduct: vanishing " | toString yz | ", nonzero " | toString ynz);
-- the rank of a set of product classes inside Ext^2, by linear algebra in the
-- internal degree zero part of the Hom complex: cycles modulo boundaries
classRank = (P, pairs) -> (
   H := Hom(P, P ** R^{-2});
   els := apply(pairs, ab -> (homomorphism' ((ksMap(P, ab#1, 1)) * (ksMap(P, ab#0, 0))))_0);
   zmat := fold(els, (u,v) -> u | v);
   Bd := super basis(0, image dd^H_(-1));
   Zd := super basis(0, ker dd^H_(-2));
   rB := rank Bd; rZ := rank Zd;
   rBZ := rank (Bd | lift(zmat, R));
   (rBZ - rB, rZ - rB));
allPairs = flatten apply(4, a -> apply(toList(a..3), b -> (a,b)));
print("(I) rank of the four mixed products, and dim Ext^2: " | toString classRank(PI, {(0,2),(0,3),(1,2),(1,3)}));
print("(I) rank of all ten products: " | toString classRank(PI, allPairs));

-- (K) the complex [R -> R/I1 (+) R/I2], resolved by the cone of the lifted map
Q = R^1/I1 ++ R^1/I2;
Fq = freeResolution Q;
C0 = complex R^1;
gt = map(Fq, C0, i -> if i == 0 then map(Fq_0, R^1, matrix{{1_R},{1_R}}) else map(Fq_i, C0_i, 0));
assert isComplexMorphism gt;
PK = cone gt;
print("homology of the model (K): H_0 = " | toString prune HH_0 PK | ",  H_1 = " | toString prune HH_1 PK);
report("(K)  K = [O -> O_{P1} (+) O_{P2}]", PK);
print("(K) rank of the two products a_1 a_2, a_3 a_4, and dim Ext^2: " | toString classRank(PK, {(0,1),(2,3)}));
print("(K) rank of all ten products: " | toString classRank(PK, allPairs));
print("done");
