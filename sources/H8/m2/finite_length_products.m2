-- finite_length_products.m2
--
-- The product of two jet classes on a complex with finite length cohomology.
--
-- Let R = Q[x_1,...,x_c], let M be a bounded complex of finitely generated
-- free graded R-modules whose cohomology has finite length, and for a
-- constant vector field a = sum a_i d/dx_i let J(a) in Ext^1(M,M) be the
-- jet class of M along a.  On M with differential d it is the degree -1
-- chain map -a(d), the entrywise derivative of the differential, exactly as
-- in local_products.m2 and lci_products.m2.  The product J(b)J(a) is the
-- composite, and it vanishes in Ext^2(M,M) exactly when the composite is
-- null homotopic.
--
-- The claim tested here is the local lemma behind the support theorem for
-- the semiregularity criterion:
--
--   if the Euler characteristic chi(M) = sum_i (-1)^i length H^i(M) is
--   nonzero and a, b are linearly independent, then J(b)J(a) is nonzero.
--
-- It is tested on finite length modules of every shape at hand (the residue
-- field, powers of the maximal ideal, monomial and non-monomial complete
-- intersections, Gorenstein and non-Gorenstein algebras, non-cyclic modules,
-- direct sums) in two and three variables, for every pair of coordinate
-- directions and for pairs of random rational directions; and on complexes
-- with several cohomology modules.
--
-- The hypothesis on chi cannot be dropped.  The last block builds the cone C
-- of the class J(x_2)J(x_1), viewed as a chain map k --> k[2] on the Koszul
-- resolution of the residue field k in two variables.  Then chi(C) = 0, and
-- the script checks that J(x_2)J(x_1) is null homotopic on C, while on the
-- split complex k (+) k[1], which also has chi = 0, it is not.  So the
-- vanishing of the Euler characteristic is necessary for the product to
-- vanish and is not sufficient.
--
-- Run:  M2 --script finite_length_products.m2   (Macaulay2 1.22, package Complexes)

needsPackage "Complexes";

-- jet chain map along the constant vector field with coefficient list v,
-- internally shifted by s so that the composites are homogeneous
jetMap = (R, P, v, s) -> (
   Ps := P ** R^{-s}; Pt := P ** R^{-s-1};
   map(Pt, Ps, i -> map(Pt_(i-1), Ps_i,
       -sum(#v, j -> v#j * diff(R_j, dd^P_i))), Degree => -1));

-- the product J(b)J(a) on P, as a chain map of homological degree -2
prodMap = (R, P, va, vb) -> (jetMap(R, P, vb, 1)) * (jetMap(R, P, va, 0));

-- Euler characteristic of a free complex with finite length cohomology
eulerChar = P -> sum(toList(min P .. max P), i -> (-1)^i * degree HH_i P);

coord = (c, j) -> apply(c, i -> if i == j then 1 else 0);
randVec = c -> apply(c, i -> random(-9, 9));

NFAIL = 0; NPASS = 0;
record = (ok, msg) -> (
   if ok then (NPASS = NPASS + 1; print("  [PASS] " | msg))
         else (NFAIL = NFAIL + 1; print("  [FAIL] " | msg)));

testComplex = (R, name, P) -> (
   c := numgens R;
   chi := eulerChar P;
   nz := {};
   for a from 0 to c-1 do for b from a+1 to c-1 do (
      g := prodMap(R, P, coord(c,a), coord(c,b));
      nz = append(nz, not isNullHomotopic g));
   -- two random directions, independent with probability one
   va := randVec c; vb := randVec c;
   while rank matrix{va, vb} < 2 do (va = randVec c; vb = randVec c);
   gr := prodMap(R, P, va, vb);
   nzr := not isNullHomotopic gr;
   allnz := all(nz, identity) and nzr;
   record(if chi != 0 then allnz else true,
      name | ":  chi = " | toString chi | ",  every product J(b)J(a) with a,b "
      | "independent is nonzero: " | toString allnz);
   (chi, allnz));

print("finite length complexes: the product of two independent jet classes");
print("");

-- two variables
R2 = QQ[x1, x2];
k2 = coker vars R2;
mods2 = {
   ("k = R/m", k2),
   ("R/m^2", R2^1 / (ideal vars R2)^2),
   ("R/m^3", R2^1 / (ideal vars R2)^3),
   ("R/(x1, x2^2)", R2^1 / ideal(x1, x2^2)),
   ("R/(x1^2, x2^3)", R2^1 / ideal(x1^2, x2^3)),
   ("R/(x1^2+x2^2, x1 x2)", R2^1 / ideal(x1^2 + x2^2, x1*x2)),
   ("R/(x1^3, x1 x2, x2^2)", R2^1 / ideal(x1^3, x1*x2, x2^2)),
   ("R/(x1^2, x1 x2^2, x2^4)", R2^1 / ideal(x1^2, x1*x2^2, x2^4)),
   ("R/(x1^3 - x2^3, x1^2 x2, x1 x2^2)",
       R2^1 / ideal(x1^3 - x2^3, x1^2*x2, x1*x2^2)),
   ("m/m^3 (not cyclic)", (ideal vars R2) * R2^1 / ((ideal vars R2)^3 * R2^1)),
   ("coker of a 2x3 matrix (not cyclic)", coker matrix{{x1, x2, 0}, {0, x1, x2}}),
   ("k (+) R/m^2", k2 ++ R2^1 / (ideal vars R2)^2)
   };
print("-- c = 2");
for m in mods2 do (
   record(dim m#1 == 0, m#0 | " has finite length");
   testComplex(R2, m#0, freeResolution m#1));

-- three variables
R3 = QQ[y1, y2, y3];
k3 = coker vars R3;
mods3 = {
   ("k = R/m", k3),
   ("R/m^2", R3^1 / (ideal vars R3)^2),
   ("R/(y1, y2, y3^2)", R3^1 / ideal(y1, y2, y3^2)),
   ("R/(y1^2, y2^2, y3^2)", R3^1 / ideal(y1^2, y2^2, y3^2)),
   ("R/(y1 y2, y2 y3, y1 y3, y1^2, y2^2, y3^3)",
       R3^1 / ideal(y1*y2, y2*y3, y1*y3, y1^2, y2^2, y3^3)),
   ("R/(y1^2 - y2^2, y2^2 - y3^2, y1 y2, y2 y3, y1 y3) (Gorenstein)",
       R3^1 / ideal(y1^2 - y2^2, y2^2 - y3^2, y1*y2, y2*y3, y1*y3))
   };
print("");
print("-- c = 3");
for m in mods3 do (
   record(dim m#1 == 0, m#0 | " has finite length");
   testComplex(R3, m#0, freeResolution m#1));

-- complexes with several cohomology modules
print("");
print("-- complexes with more than one cohomology module, c = 2");
K = freeResolution k2;
Q2 = freeResolution(R2^1 / (ideal vars R2)^2);
testComplex(R2, "k (+) k[1] (+) k", K ++ K[1] ++ K);
testComplex(R2, "R/m^2 (+) k[1]", Q2 ++ K[1]);
testComplex(R2, "R/m^2 (+) k[1] (+) k[1]", Q2 ++ K[1] ++ K[1]);

-- the sharpness example: the cone of J(x2)J(x1) on the Koszul complex
print("");
print("-- sharpness: chi = 0 is necessary for the product to vanish, and not sufficient");
g = prodMap(R2, K, coord(2,0), coord(2,1));   -- K --> K ** R^{-2}, degree -2
Kt = K ** R2^{-2};
-- the cone C with C_i = Kt_(i-2) (+) K_(i-1), d = [[d, g],[0, -d]]
lo = min K; hi = max K + 2;
Cmods = hashTable apply(toList(lo .. hi+1), i -> i =>
   (if i-2 >= min Kt and i-2 <= max Kt then Kt_(i-2) else R2^0) ++
   (if i-1 >= min K and i-1 <= max K then K_(i-1) else R2^0));
Cdiff = hashTable apply(toList(lo+1 .. hi+1), i -> i => (
   src := Cmods#i; tgt := Cmods#(i-1);
   a11 := if i-2 > min Kt and i-2 <= max Kt then dd^Kt_(i-2)
          else map((if i-3 >= min Kt and i-3 <= max Kt then Kt_(i-3) else R2^0),
                   (if i-2 >= min Kt and i-2 <= max Kt then Kt_(i-2) else R2^0), 0);
   a12 := if i-1 >= min K and i-1 <= max K and i-3 >= min Kt then g_(i-1)
          else map((if i-3 >= min Kt and i-3 <= max Kt then Kt_(i-3) else R2^0),
                   (if i-1 >= min K and i-1 <= max K then K_(i-1) else R2^0), 0);
   a22 := if i-1 > min K and i-1 <= max K then -dd^K_(i-1)
          else map((if i-2 >= min K and i-2 <= max K then K_(i-2) else R2^0),
                   (if i-1 >= min K and i-1 <= max K then K_(i-1) else R2^0), 0);
   a21 := map((if i-2 >= min K and i-2 <= max K then K_(i-2) else R2^0),
              (if i-2 >= min Kt and i-2 <= max Kt then Kt_(i-2) else R2^0), 0);
   map(tgt, src, matrix{{a11, a12}, {a21, a22}})));
C = complex(apply(toList(lo+1 .. hi+1), i -> Cdiff#i), Base => lo);
record(isWellDefined C, "the cone of J(x2)J(x1) on the Koszul complex is a complex");
record(eulerChar C == 0, "its Euler characteristic is " | toString eulerChar C);
record(all(toList(min C .. max C), i -> dim HH_i C <= 0),
   "its cohomology has finite length, lengths " |
   toString apply(toList(min C .. max C), i -> degree HH_i C));
gC = prodMap(R2, C, coord(2,0), coord(2,1));
record(isNullHomotopic gC, "on the cone, J(x2)J(x1) is null homotopic");
gS = prodMap(R2, K ++ K[1], coord(2,0), coord(2,1));
record(not isNullHomotopic gS, "on the split complex k (+) k[1], also of Euler "
   | "characteristic zero, J(x2)J(x1) is not null homotopic");

print("");
print(toString NPASS | " checks passed, " | toString NFAIL | " failed");
if NFAIL > 0 then exit 1;
