-- lci_products.m2
--
-- Where the local obstruction of Theorem 14.110 actually lives.  Item (XXXI).
--
-- The germ comparison of Lemma 14.108 compares the germs of the two sides of
--
--   At(F)^2 = -d Theta^2 . id .
--
-- The right side has no germ at all in Ext^2, so the comparison can only
-- decide when the left side has one, that is when the local Ext^2 of the germ
-- of F is nonzero.  This script determines, for a list of codimension two
-- germs in C^4, whether Ext^2(I,I) vanishes, and it finds that it vanishes
-- exactly at the germs whose local ring is Cohen-Macaulay.  That is not the
-- complete intersection property: two of the germs below need three
-- generators in codimension two and still have Ext^2 = 0.  By
-- Auslander-Buchsbaum a codimension two germ is Cohen-Macaulay exactly when
-- pdim R/I = 2, that is pdim I = 1, and Ext^q(I,-) vanishes above pdim I.
--
-- For each germ the script reports
--   * the number of minimal generators of the ideal and its codimension, so
--     that lci is visible as "two generators in codimension two";
--   * the ranks of a minimal free resolution;
--   * Ext^1(I,I) and Ext^2(I,I);
--   * for the germs with Ext^2 nonzero, which products a_a * a_b of the
--     translation Kodaira-Spencer classes are nonzero there.
--
-- The models, all of codimension two in C^4:
--
--   smooth          (x1, x2)                          CM
--   curve meeting   (x1, x2 x3)      two planes along a line, CM
--   triple curve    (x1, x2 x3 x4)   three planes along a line, CM
--   double plane    (x1^2, x2)                        CM, not reduced
--   quadric cone    (x1, x2^2 - x3 x4)                CM, singular
--   fat plane       (x1,x2)^2            CM, three generators, not reduced
--   cubic cone      minors of [[x1,x2,x3],[x2,x3,x4]]
--                                        CM, three generators, irreducible
--   point meeting   (x1,x2) cap (x3,x4)               not CM: pdim 3
--   three at a point                                  not CM: pdim 3
--   embedded point  (x1,x2) cap m^2                   not CM: pdim 4
--
-- The conventions for the jet maps are those of local_products.m2, which this
-- script reuses: on a free resolution P of F with differential d, the
-- contraction of the Atiyah class with the derivation d/dx_a is the degree -1
-- chain map -D(d), and the Yoneda product of two such is the composite, which
-- is zero in Ext^2 exactly when the composite is null homotopic.
--
-- Run:  M2 --script lci_products.m2      (Macaulay2 1.22, package Complexes)

needsPackage "Complexes";
R = QQ[x1,x2,x3,x4];

ksMap = (P, a, s) -> (
   Ps := P ** R^{-s}; Pt := P ** R^{-s-1};
   map(Pt, Ps, i -> map(Pt_(i-1), Ps_i, -diff(R_a, dd^P_i)), Degree => -1));

report = (name, I) -> (
   print("");
   print("== " | name | " ==");
   g := numgens trim I;
   c := codim I;
   print("  minimal generators " | toString g | ", codimension " | toString c
         | ", complete intersection: " | toString (g == c));
   pd := pdim (R^1/I);
   print("  pdim R/I = " | toString pd | ", codim = " | toString c
         | ", Cohen-Macaulay: " | toString (pd == c));
   P := freeResolution(module I);
   print("  resolution ranks " | toString apply(toList(min P..max P), i -> rank P_i));
   E1 := prune HH_(-1) Hom(P, P);
   E2 := prune HH_(-2) Hom(P, P);
   E3 := prune HH_(-3) Hom(P, P);
   print("  Ext^1(I,I) = " | toString E1);
   print("  Ext^2(I,I) = " | toString E2 | "     zero: " | toString (E2 == 0));
   print("  Ext^3(I,I) = " | toString E3 | "     zero: " | toString (E3 == 0));
   if E2 != 0 then (
      nonzeros := {};
      for a from 0 to 3 do for b from a to 3 do (
         h := (ksMap(P, b, 1)) * (ksMap(P, a, 0));
         if not isNullHomotopic h then nonzeros = append(nonzeros, (a+1,b+1));
      );
      print("  products a_a a_b that are nonzero: " | toString nonzeros);
   ) else (
      print("  no products to test: the local Ext^2 is zero");
   );
);

print("(XXXI) the local Ext^2 of a codimension two germ, and where it lives");

report("smooth              (x1, x2)", ideal(x1,x2));
report("two planes, a line  (x1, x2 x3)", ideal(x1, x2*x3));
report("three planes, a line (x1, x2 x3 x4)", ideal(x1, x2*x3*x4));
report("double plane        (x1^2, x2)", ideal(x1^2, x2));
report("quadric cone        (x1, x2^2 - x3 x4)", ideal(x1, x2^2 - x3*x4));
report("two planes, a point (x1,x2) cap (x3,x4)",
       intersect(ideal(x1,x2), ideal(x3,x4)));
report("fat plane           (x1,x2)^2", (ideal(x1,x2))^2);
report("cone on the twisted cubic",
       minors(2, matrix{{x1,x2,x3},{x2,x3,x4}}));
report("three planes, pairwise a point",
       intersect(ideal(x1,x2), ideal(x3,x4), ideal(x1-x3,x2-x4)));
report("plane with an embedded point",
       intersect(ideal(x1,x2), (ideal(x1,x2,x3,x4))^2));

print("");
print("Summary: Ext^2(I,I) = 0 at every Cohen-Macaulay germ, whether or not it");
print("is a complete intersection, whether or not it is reduced, and whether or");
print("not it is irreducible; and Ext^2(I,I) != 0 at the germs that are not");
print("Cohen-Macaulay.  The reason is Auslander-Buchsbaum: a codimension two");
print("germ is Cohen-Macaulay exactly when pdim R/I = 2, that is pdim I = 1,");
print("and Ext^q(I,-) vanishes for q above the projective dimension of I.");
print("So the germ comparison of Lemma 14.108 can decide only at a point where");
print("the support fails to be Cohen-Macaulay.");
