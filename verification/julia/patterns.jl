# Block patterns of cor:patterns and the homomorphism nu_R of lem:nusqrt.
# Same checks and output as verification/python/patterns.py.

const ROWS = [
    (114, 3, [51, 21, 86, 14, 56],
     [([0, 0, 1, 2, 0], 1), ([0, 0, 2, 0, 1], 1), ([1, 3, 0, 0, 0], 1), ([2, 0, 0, 1, 2], 1)]),
    (114, 24, [1, 25, 43, 57, 102],
     [([3, 1, 2, 0, 0], 7), ([0, 1, 5, 0, 1], 2), ([0, 0, 0, 2, 0], 12), ([1, 5, 0, 0, 1], 3),
      ([0, 0, 0, 0, 19], 1)]),
    (44, 11, [1, 5, 8, 33, 41],
     [([3, 0, 0, 0, 1], 1), ([0, 0, 11, 0, 0], 1), ([1, 1, 0, 0, 2], 5), ([1, 2, 0, 1, 0], 3),
      ([0, 0, 0, 4, 0], 2)]),
    (52, 14, [1, 5, 16, 37, 45],
     [([0, 0, 0, 3, 1], 4), ([0, 1, 1, 0, 3], 1), ([2, 1, 0, 0, 1], 7), ([0, 0, 13, 0, 0], 1),
      ([0, 3, 0, 1, 0], 2)]),
    (52, 5, [1, 6, 14, 34, 49],
     [([0, 0, 5, 1, 0], 1), ([3, 0, 0, 0, 1], 1), ([2, 0, 0, 3, 0], 1), ([0, 3, 0, 1, 0], 1),
      ([0, 1, 0, 0, 2], 2)]),
    (102, 6, [1, 34, 44, 56, 69],
     [([0, 0, 0, 3, 2], 1), ([0, 0, 3, 0, 4], 1), ([0, 3, 0, 0, 0], 2), ([2, 0, 1, 1, 0], 3)]),
    (102, 18, [5, 35, 51, 96, 17],
     [([0, 0, 0, 0, 6], 2), ([0, 0, 0, 17, 0], 1), ([0, 0, 2, 0, 0], 9), ([0, 6, 0, 1, 0], 1),
      ([3, 2, 0, 0, 1], 6)]),
]

const LEVELS = [(33, (3, 11), [1, 4, 16, 22, 25, 31]), (39, (3, 13), [1, 7, 16, 22, 34, 37])]

ok = true
function fail(msg)
    global ok = false
    println("FAIL ", msg)
end

jn(v) = join(string.(v), ",")

for (m, D, a, cols) in ROWS
    if !(length(a) == 5 && all(x -> 0 < x < m, a) && sum(a) == 2m)
        fail("character $(jn(a)) at level $m")
    end
    sums = [sum(e[k] * d for (e, d) in cols) for k in 1:5]
    sums == fill(D, 5) || fail("(P1) for $(jn(a)): column sums $(jn(sums))")
    weights = Int[]
    for (e, d) in cols
        w = sum(a .* e)
        push!(weights, w)
        (d > 0 && any(x -> x > 0, e) && any(x -> x == 0, e) && w % m == 0) ||
            fail("(P2) for $(jn(a)), column $(jn(e))")
    end
    degs = sum(d for (_, d) in cols)
    degs > D || fail("(P3) for $(jn(a))")
    println("m=$m alpha=($(jn(a))) D=$D degrees=$degs weights=$(jn(weights))")
end

for (M, primes, O) in LEVELS
    roots = [y for y in 0:M-1 if y * y % M == 1]
    nu(v) = count(y -> y * y % M == 1, v) % 2
    for t in 1:M-1
        if gcd(t, M) == 1 && sum(t * x % M for x in O) != 3M
            fail("O_$M is not balanced at t=$t")
        end
    end
    nu(O) == 1 || fail("nu_R(O_$M) = 0")
    for y in 1:M-1
        nu([y, M - y]) == 0 || fail("nu_R on the pair ($y,$(M - y))")
    end
    nstd = 0
    for p in primes
        d = M ÷ p
        for i in 1:d-1
            s = vcat([i + k * d for k in 0:p-1], [mod(-p * i, M)])
            nstd += 1
            nu(s) == 0 || fail("nu_R on sigma_{$p,$i}")
        end
    end
    inO = [y for y in O if y in roots]
    println("M=$M roots=$(jn(roots)) O=($(jn(O))) in_O=$(jn(inO)) nu_R(O)=$(nu(O)) standard=$nstd pairs=$(M - 1)")
end

ok || exit(1)
println("7 block patterns and nu_R at levels 33, 39: all checks passed")
