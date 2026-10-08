-- Max Noether's theorem on explicit plane curves.
--
-- For a non-hyperelliptic curve C of genus g the multiplication map
-- Sym^2 H^0(K) -> H^0(2K) is onto, so its kernel I_2, the quadrics through
-- the canonical curve, has dimension g(g+1)/2 - (3g-3) = (g-2)(g-3)/2.  The
-- map is the codifferential of the Torelli map at C, and I_2 is the conormal
-- space of the Jacobian locus in A_g at J(C): the first-order directions in
-- which the Abel-Jacobi curve cannot follow a deformation of J(C).  The paper
-- uses this as the model for Schoen's subvariety (Section 5.6).
--
-- Curves are taken with small integer coefficients and computed modulo a
-- large prime p.  Smoothness and the rank of a matrix with integer entries
-- can only drop modulo p, so a smooth curve of full rank modulo p is smooth
-- and of full rank over Q.  On a smooth plane curve of degree d, K = O(d-3)
-- and H^0(2K) is the space of forms of degree 2d-6 modulo multiples of the
-- equation.

p = 32003;
kk = ZZ/p;
setRandomSeed 20261008;
rnd = () -> random(-9, 9);

-- the rank of the span of a list of polynomials of one degree
spanRank = L -> (
    if #L == 0 then return 0;
    M := sub(last coefficients matrix {L}, kk);
    rank M);

-- plane curves of degree d, genus (d-1)(d-2)/2
noether = d -> (
    R := kk[x,y,z];
    f := sum apply(flatten entries basis(d, R), mm -> rnd() * mm);
    assert(dim ideal(f, jacobian ideal f) == 0);  -- smooth
    g := (d-1)*(d-2)//2;
    K := flatten entries basis(d-3, R);            -- H^0(K) = forms of degree d-3
    prods := flatten apply(#K, i -> apply(toList(i..#K-1), j -> K#i * K#j));
    fm := if d >= 6 then apply(flatten entries basis(d-6, R), mm -> f*mm) else {};
    -- products of degree 2d-6 modulo f: the rank of the image in H^0(2K)
    img := spanRank(prods | fm) - spanRank fm;
    assert(img == 3*g - 3);
    ker := #prods - img;
    assert(ker == (g-2)*(g-3)//2);
    print("N plane,d=" | toString d | ",g=" | toString g | ",dim_I2 " | toString ker);
    )

scan({4, 5, 6, 7, 8}, noether);
