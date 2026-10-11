# Finite checks for the Fermat varieties of degree 51 (level 102); see python/fermat51.py.
# The output is line for line that of the Python program (without --lattice) and of C.

const M = 102
const ALPHA = [1, 7, 51, 60, 85]
const ALPHA2 = [91, 34, 26, 98, 57]
const BETA = vcat(ALPHA, ALPHA2)
# family A (degree 6) for 37 alpha': blocks s, t, Q, F; family B (degree 18) for 5 alpha
const FAMA = [("s", [0, 0, 0, 3, 2], 1), ("t", [0, 0, 3, 0, 4], 1), ("Q", [0, 3, 0, 0, 0], 2),
              ("F", [2, 0, 1, 1, 0], 3)]
const FAMB = [("Q", [0, 0, 0, 0, 6], 2), ("t", [0, 0, 0, 17, 0], 1), ("F", [0, 0, 2, 0, 0], 9),
              ("s", [0, 6, 0, 1, 0], 1), ("G", [3, 2, 0, 0, 1], 6)]

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
    @assert all(x % M != 0 for x in BETA) && sum(ALPHA) == 2M && sum(ALPHA2) == 3M
    U = units(M)
    na = [normt(ALPHA, t) for t in U]
    nb = [normt(ALPHA2, t) for t in U]
    @assert all(x in (2, 3) for x in vcat(na, nb)) && all(na .+ nb .== 5)
    a5 = [5 * x % M for x in ALPHA]
    a37 = [37 * x % M for x in ALPHA2]
    @assert a5 == [5, 35, 51, 96, 17] && normt(a5, 1) == 2
    @assert a37 == [1, 34, 44, 56, 69] && normt(a37, 1) == 2
    push!(lines, "alpha $(tup(ALPHA)) |alpha| = $(normt(ALPHA, 1)), 5 alpha = $(tup(a5)) with |5 alpha| = 2, |t alpha| in {2,3} for all $(length(na)) units, $(count(==(2), na)) of them 2")
    push!(lines, "alpha' $(tup(ALPHA2)), 37 alpha' = $(tup(a37)) with |37 alpha'| = 2, |t alpha| + |t alpha'| = 5 for all $(length(nb)) units")
    push!(lines, "units t < 51: " * join(["$t:$(x)$(y)" for (t, x, y) in zip(U, na, nb) if t < 51], " "))
    @assert !any((BETA[i] + BETA[j]) % M == 0 for i in 1:10 for j in i+1:10)
    @assert all(sum(t * x % M for x in BETA) == 5M for t in U)
    push!(lines, "beta = alpha * alpha': |t beta| = 5 for all units t, no pair: Hodge character of X^8_102")
end

function parity!(lines)
    o17 = [y for y in BETA if order(y) == 17]
    @assert o17 == [60]
    push!(lines, "nu_17(beta) = 1: the only entry of order 17 is $(o17[1])")
    gens = vcat([[y, M - y] for y in 1:M-1], standard(M))
    @assert !any(isodd(count(y -> order(y) == 17, g)) for g in gens)
    push!(lines, "nu_17 vanishes on S_102: $(M - 1) pairs and $(length(standard(M))) standard characters checked")
end

# nondecreasing h-tuples of nonzero residues
function halves(h)
    out = [Int[]]
    for _ in 1:h
        out = [vcat(a, [x]) for a in out for x in (isempty(a) ? 1 : a[end]):M-1]
    end
    out
end

# A balanced multiset of k elements, sorted, splits into its k/2 smallest and k/2 largest
# elements A and C with f(A) + f(C) = (k/2) M, f(A)_t = sum <t a>; the halves are matched by f.
function small_multisets!(lines)
    U = units(M)
    for k in (4, 6)
        h = k ÷ 2
        hs = halves(h)
        f(a) = [sum(t * x % M for x in a) for t in U]
        table = Dict{Vector{Int},Vector{Vector{Int}}}()
        for a in hs
            push!(get!(table, f(a), Vector{Int}[]), a)
        end
        cnt = 0
        odd = 0
        for a in hs
            want = h * M .- f(a)
            for c in get(table, want, Vector{Int}[])
                if c[1] >= a[end]
                    cnt += 1
                    odd += count(y -> order(y) == 17, vcat(a, c)) % 2
                end
            end
        end
        @assert odd == 0
        push!(lines, "balanced multisets of $k nonzero residues mod 102: $cnt, all with nu_17 = 0")
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
        push!(lines, "family $name block $bname (degree $d) exponents $(tup(e)) weight $w = $(w ÷ M)*102")
    end
    @assert all(degs .== D) && adeg == 2D
end

lines = String[]
characters!(lines)
parity!(lines)
small_multisets!(lines)
family!(lines, "A", [1, 34, 44, 56, 69], FAMA, 6)
@assert !any(e[1] > 0 && e[5] > 0 for (_, e, _) in FAMA)
push!(lines, "family A: every u_k has degree 6, A has degree 12; (0,4) shares no block")
family!(lines, "B", [5, 35, 51, 96, 17], FAMB, 18)
@assert !any(e[3] > 0 && e[4] > 0 for (_, e, _) in FAMB)
push!(lines, "family B: every u_k has degree 18, A has degree 36; (2,3) shares no block")
foreach(println, lines)
println("$(length(lines)) lines, all checks passed")
