# Finite checks for the Fermat varieties of degree 44; see python/fermat44.py.
# The output is line for line that of the Python program (without --lattice) and of C.

const M = 44
const ALPHA = [1, 5, 8, 33, 41]
const B = [9, 37, 42]
const BETA = vcat(ALPHA, B)
# blocks s, t, P, Q, S: exponents in (u0, ..., u4) and degrees
const FAM = [("s", [3, 0, 0, 0, 1], 1), ("t", [0, 0, 11, 0, 0], 1), ("P", [1, 1, 0, 0, 2], 5),
             ("Q", [1, 2, 0, 1, 0], 3), ("S", [0, 0, 0, 4, 0], 2)]

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
    @assert all(x % M != 0 for x in BETA) && sum(ALPHA) % M == 0 && sum(B) % M == 0
    U = units(M)
    na = [normt(ALPHA, t) for t in U]
    nb = [normt(B, t) for t in U]
    @assert all(na .+ nb .== 4) && normt(ALPHA, 1) == 2
    push!(lines, "alpha $(tup(ALPHA)) |alpha| = $(normt(ALPHA, 1)), |t alpha| in {2,3} for all $(length(na)) units, $(count(==(2), na)) of them 2")
    push!(lines, "b $(tup(B)) |b| = $(normt(B, 1)), |t alpha| + |t b| = 4 for all $(length(nb)) units")
    push!(lines, "units t < 22: " * join(["$t:$(x)$(y)" for (t, x, y) in zip(U, na, nb) if t < 22], " "))
    @assert !any((BETA[i] + BETA[j]) % M == 0 for i in 1:8 for j in i+1:8)
    @assert all(2 * sum(t * x % M for x in BETA) == 8M for t in U)
    push!(lines, "beta = alpha * b: |t beta| = 4 for all units t, no pair: Hodge character of X^6_44")
end

function parity!(lines)
    o11 = [y for y in BETA if order(y) == 11]
    @assert o11 == [8]
    push!(lines, "nu_11(beta) = 1: the only entry of order 11 is $(o11[1])")
    gens = vcat([[y, M - y] for y in 1:M-1], standard(M))
    @assert !any(isodd(count(y -> order(y) == 11, g)) for g in gens)
    push!(lines, "nu_11 vanishes on S_44: $(M - 1) pairs and $(length(standard(M))) standard characters checked")
end

function small_multisets!(lines)
    U = units(M)
    for k in (4, 6)
        cnt = 0
        odd = 0
        a = zeros(Int, k)
        function rec(pos, lo)
            if pos > k
                sum(a) % M == 0 || return
                all(2 * sum(t * x % M for x in a) == k * M for t in U) || return
                cnt += 1
                odd += count(y -> order(y) == 11, a) % 2
                return
            end
            for x in lo:M-1
                a[pos] = x
                rec(pos + 1, x)
            end
        end
        rec(1, 1)
        @assert odd == 0
        push!(lines, "balanced multisets of $k nonzero residues mod 44: $cnt, all with nu_11 = 0")
    end
end

function family!(lines)
    degs = zeros(Int, 5)
    adeg = 0
    for (name, e, d) in FAM
        w = sum(ALPHA .* e)
        @assert w % M == 0 && any(e .> 0) && any(e .== 0)
        adeg += (w ÷ M) * d
        degs .+= e .* d
        push!(lines, "family block $name (degree $d) exponents $(tup(e)) weight $w = $(w ÷ M)*44")
    end
    @assert all(degs .== 11) && adeg == 22
    push!(lines, "family: every u_k has degree 11, A has degree 22; (0,2) shares no block")
end

lines = String[]
characters!(lines)
parity!(lines)
small_multisets!(lines)
family!(lines)
foreach(println, lines)
println("$(length(lines)) lines, all checks passed")
