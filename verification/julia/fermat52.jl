# Finite checks for the Fermat varieties of degree 52; see python/fermat52.py.
# The output is line for line that of the Python program (without --lattice) and of C.

const M = 52
const ALPHA = [1, 5, 16, 37, 45]
const ALPHA2 = [29, 18, 42, 50, 17]
const BETA = vcat(ALPHA, ALPHA2)
# family A (degree 14) for alpha: blocks G, s, F, t, H; family B (degree 5) for 9 alpha'
const FAMA = [("G", [0, 0, 0, 3, 1], 4), ("s", [0, 1, 1, 0, 3], 1), ("F", [2, 1, 0, 0, 1], 7),
              ("t", [0, 0, 13, 0, 0], 1), ("H", [0, 3, 0, 1, 0], 2)]
const FAMB = [("t", [0, 0, 5, 1, 0], 1), ("s", [3, 0, 0, 0, 1], 1), ("s-t", [2, 0, 0, 3, 0], 1),
              ("L", [0, 3, 0, 1, 0], 1), ("Q", [0, 1, 0, 0, 2], 2)]

units(m) = [t for t in 1:m-1 if gcd(t, m) == 1]
normt(a, t) = sum(t * x % M for x in a) ÷ M
order(y) = M ÷ gcd(y, M)
tup(a) = "(" * join(string.(a), ", ") * ")"

function standard(m)
    out = Vector{Vector{Int}}()
    for p in [q for q in 2:m if m % q == 0 && all(q % r != 0 for r in 2:q-1)]
        m == p && continue
        d = m ÷ p
        for i in 1:d-1
            if p == 2
                push!(out, [i, i + d, mod(-2i, m), d])
            else
                push!(out, vcat([i + j * d for j in 0:p-1], [mod(-p * i, m)]))
            end
        end
    end
    out
end

function characters!(lines)
    @assert all(x % M != 0 for x in BETA) && sum(ALPHA) % M == 0 && sum(ALPHA2) % M == 0
    U = units(M)
    na = [normt(ALPHA, t) for t in U]
    nb = [normt(ALPHA2, t) for t in U]
    @assert all(x in (2, 3) for x in vcat(na, nb)) && all(na .+ nb .== 5)
    a9 = [9 * x % M for x in ALPHA2]
    @assert normt(ALPHA, 1) == 2 && a9 == [1, 6, 14, 34, 49] && normt(a9, 1) == 2
    push!(lines, "alpha $(tup(ALPHA)) |alpha| = $(normt(ALPHA, 1)), |t alpha| in {2,3} for all $(length(na)) units, $(count(==(2), na)) of them 2")
    push!(lines, "alpha' $(tup(ALPHA2)), 9 alpha' = $(tup(a9)) with |9 alpha'| = 2, |t alpha| + |t alpha'| = 5 for all $(length(nb)) units")
    push!(lines, "units t < 26: " * join(["$t:$(x)$(y)" for (t, x, y) in zip(U, na, nb) if t < 26], " "))
    @assert !any((BETA[i] + BETA[j]) % M == 0 for i in 1:10 for j in i+1:10)
    @assert all(sum(t * x % M for x in BETA) == 5M for t in U)
    push!(lines, "beta = alpha * alpha': |t beta| = 5 for all units t, no pair: Hodge character of X^8_52")
end

function parity!(lines)
    o13 = [y for y in BETA if order(y) == 13]
    @assert o13 == [16]
    push!(lines, "nu_13(beta) = 1: the only entry of order 13 is $(o13[1])")
    gens = vcat([[y, M - y] for y in 1:M-1], standard(M))
    @assert !any(isodd(count(y -> order(y) == 13, g)) for g in gens)
    push!(lines, "nu_13 vanishes on S_52: $(M - 1) pairs and $(length(standard(M))) standard characters checked")
end

function small_multisets!(lines)
    U = units(M)
    for k in (4, 6)
        cnt = 0
        odd = 0
        a = zeros(Int, k)
        function rec(pos, lo, s)
            if pos > k
                s % M == 0 || return
                all(2 * sum(t * x % M for x in a) == k * M for t in U) || return
                cnt += 1
                odd += count(y -> order(y) == 13, a) % 2
                return
            end
            for x in lo:M-1
                a[pos] = x
                rec(pos + 1, x, s + x)
            end
        end
        rec(1, 1, 0)
        @assert odd == 0
        push!(lines, "balanced multisets of $k nonzero residues mod 52: $cnt, all with nu_13 = 0")
    end
end

function family!(lines, name, al, fam, D)
    degs = zeros(Int, 5)
    adeg = 0
    for (bname, e, d) in fam
        w = sum(al .* e)
        @assert w % M == 0 && any(e .> 0) && any(e .== 0)
        adeg += (w ÷ M) * d
        degs .+= e .* d
        push!(lines, "family $name block $bname (degree $d) exponents $(tup(e)) weight $w = $(w ÷ M)*52")
    end
    @assert all(degs .== D) && adeg == 2D
end

lines = String[]
characters!(lines)
parity!(lines)
small_multisets!(lines)
family!(lines, "A", ALPHA, FAMA, 14)
@assert !any(e[1] > 0 && e[3] > 0 for (_, e, _) in FAMA)
push!(lines, "family A: every u_k has degree 14, A has degree 28; (0,2) shares no block")
family!(lines, "B", [1, 6, 14, 34, 49], FAMB, 5)
@assert !any(e[2] > 0 && e[3] > 0 for (_, e, _) in FAMB)
push!(lines, "family B: every u_k has degree 5, A has degree 10; (1,2) shares no block")
foreach(println, lines)
println("$(length(lines)) lines, all checks passed")
