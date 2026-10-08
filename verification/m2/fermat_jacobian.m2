-- Primitive Hodge numbers of Fermat hypersurfaces from the Jacobian ring.
--
-- For a smooth hypersurface X of degree m in P^(n+1), Griffiths' residue
-- theorem gives h^(n-q,q)_prim(X) = dim R_((q+1)m-(n+2)), where R is the
-- Jacobian ring.  For the Fermat polynomial sum x_i^m, R is
-- k[x_0..x_(n+1)]/(x_0^(m-1), ..., x_(n+1)^(m-1)).  The middle number
-- h^(n/2,n/2)_prim must equal the number of characters a with <a> = n/2+1
-- that verification/python/closure_checks.py prints as h_mid_prim, and the
-- sum of all of them must equal b_prim.  Lines are printed in that format.

fermatLine = (n, m) -> (
    S := QQ[x_0..x_(n+1)];
    R := S / ideal apply(n+2, i -> x_i^(m-1));
    h := q -> (
        d := (q+1)*m - (n+2);
        if d < 0 then 0 else hilbertFunction(d, R));
    hs := apply(n+1, q -> h q);
    mid := hs#(n//2);
    total := sum hs;
    print("F n=" | toString n | ",m=" | toString m | ",b_prim " | toString total);
    print("F n=" | toString n | ",m=" | toString m | ",h_mid_prim " | toString mid);
    )

scan(2..12, m -> fermatLine(2, m));
scan(2..8, m -> fermatLine(4, m));
