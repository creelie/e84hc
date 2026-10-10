# Finite checks for the Fermat varieties of degree 114; see python/fermat114.py.
# The output is line for line that of the Python program (with --common, that of C too).

const M = 114
const ALPHA1 = [1, 25, 43, 57, 102]
const ALPHA2 = [39, 63, 68, 80, 92]
const BETA = vcat(ALPHA1, ALPHA2)
const ALPHA2T = [13 * x % M for x in ALPHA2]
const Q = Rational{BigInt}

units(m) = [t for t in 1:m-1 if gcd(t, m) == 1]
normt(a, t) = sum(t * x % M for x in a) ÷ M
order(y) = M ÷ gcd(y, M)
tup(a) = "(" * join(string.(a), ", ") * ")"
fr(x::Q) = denominator(x) == 1 ? string(numerator(x)) : string(numerator(x), "/", denominator(x))

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
    for (name, a) in (("alpha1", ALPHA1), ("alpha2", ALPHA2), ("13*alpha2", ALPHA2T))
        @assert all(x % M != 0 for x in a) && sum(a) % M == 0
        @assert !any((a[i] + a[j]) % M == 0 for i in 1:5 for j in i+1:5)
        ns = [normt(a, t) for t in units(M)]
        @assert all(n in (2, 3) for n in ns)
        push!(lines, "$name $(tup(a)) |a| = $(normt(a, 1)), |ta| in {2,3} for all $(length(ns)) units, $(count(==(2), ns)) of them 2")
    end
    @assert normt(ALPHA1, 1) == 2 && normt(ALPHA2T, 1) == 2
    @assert all(normt(ALPHA1, t) + normt(ALPHA2, t) == 5 for t in units(M))
    @assert !any((BETA[i] + BETA[j]) % M == 0 for i in 1:10 for j in i+1:10)
    push!(lines, "beta = alpha1 * alpha2: |t beta| = 5 for all units t, no pair: Hodge character of X^8_114")
end

function parity!(lines)
    o19 = [y for y in BETA if order(y) == 19]
    @assert o19 == [102]
    push!(lines, "nu_19(beta) = 1: the only entry of order 19 is $(o19[1])")
    gens = vcat([[y, M - y] for y in 1:M-1], standard(M))
    @assert !any(isodd(count(y -> order(y) == 19, g)) for g in gens)
    push!(lines, "nu_19 vanishes on S_114: $(M - 1) pairs and $(length(standard(M))) standard characters checked")
end

function families!(lines)
    fam1 = [("0", [0, 0, 1, 2, 0]), ("1", [0, 0, 2, 0, 1]), ("lambda", [1, 3, 0, 0, 0]), ("inf", [2, 0, 0, 1, 2])]
    for (blk, e) in fam1
        w = sum(ALPHA2T .* e); @assert w % M == 0
        push!(lines, "family I block $blk exponents $(tup(e)) weight $w = $(w ÷ M)*114")
    end
    @assert all(sum(e[k] for (_, e) in fam1) == 3 for k in 1:5)
    push!(lines, "family I: every u_k has degree 3, A has degree 6")
    fam2 = [("F", [3, 1, 2, 0, 0], 7), ("H", [0, 1, 5, 0, 1], 2), ("G", [0, 0, 0, 2, 0], 12),
            ("K", [1, 5, 0, 0, 1], 3), ("t", [0, 0, 0, 0, 19], 1)]
    degs = zeros(Int, 5); adeg = 0
    for (blk, e, d) in fam2
        w = sum(ALPHA1 .* e); @assert w % M == 0
        push!(lines, "family II block $blk (degree $d) exponents $(tup(e)) weight $w = $(w ÷ M)*114")
        degs .+= e .* d; adeg += (w ÷ M) * d
    end
    @assert degs == fill(24, 5) && adeg == 48
    push!(lines, "family II: every u_k has degree 24, A has degree 48")
end

# polynomials: coefficient vectors, index 1 = constant term
pmul(p, q) = (r = zeros(Q, length(p) + length(q) - 1); for i in eachindex(p), j in eachindex(q); r[i+j-1] += p[i] * q[j]; end; r)
function padd(ps...)
    r = zeros(Q, maximum(length.(ps)))
    for p in ps, i in eachindex(p); r[i] += p[i]; end
    r
end
ppow(p, e) = (r = Q[1]; for _ in 1:e; r = pmul(r, p); end; r)
pder(p) = length(p) == 1 ? Q[0] : [Q(i - 1) * p[i] for i in 2:length(p)]
coef(p, i) = i <= length(p) ? p[i] : Q(0)
shift(p, x0) = (r = Q[0]; for a in reverse(p); r = padd(pmul(r, Q[x0, 1]), Q[a]); end; r)

function residue1(lam::Q)
    L = Q[-lam, 1]
    base = [L, ppow(L, 3), pmul(Q[0, 1], ppow(Q[-1, 1], 2)), Q[0, 0, 1], Q[-1, 1]]
    dbase = [Q[-1], -3 .* ppow(L, 2), Q[0], Q[0], Q[0]]
    A = [coef(base[k], i) for i in 1:4, k in 2:5]
    c = vcat(Q(1), A \ [-coef(base[1], i) for i in 1:4])
    rhs = padd([c[k] .* dbase[k] for k in 1:5]...)
    cd = vcat(Q(0), A \ [-coef(rhs, i) for i in 1:4])
    u = [c[k] .* base[k] for k in 1:5]
    ud = [padd(cd[k] .* base[k], c[k] .* dbase[k]) for k in 1:5]
    @assert all(iszero, padd(u...))
    r = (1, 4, 5)
    a, b, cc = u[r[1]], u[r[2]], u[r[3]]
    d, e, f = ud[r[1]], ud[r[2]], ud[r[3]]
    g, h, i = pder(a), pder(b), pder(cc)
    Dt = padd(pmul(a, padd(pmul(e, i), -pmul(f, h))), -pmul(b, padd(pmul(d, i), -pmul(f, g))),
              pmul(cc, padd(pmul(d, h), -pmul(e, g))))
    Apol = pmul(pmul(Q[0, 1], Q[-lam, 1]), ppow(Q[-1, 1], 2))
    num = shift(pmul(Apol, Dt), lam)
    den = shift(pmul(pmul(pmul(pmul(u[1], u[2]), u[3]), u[4]), u[5]), lam)
    k = findfirst(!iszero, den) - 1
    @assert k == 4
    W = den[k+1:end]
    inv = [1 / W[1]]
    for n in 1:k-1
        push!(inv, -sum(W[j+1] * inv[n-j+1] for j in 1:min(n, length(W) - 1)) / W[1])
    end
    return c, sum(coef(num, j + 1) * inv[k-j] for j in 0:k-1)
end

closed_form(l) = -(l^3 - 3l^2 + 1) * (2l^3 + 12l^2 - 21l + 8) / (l * (l - 1)^2 * (3l - 2) * (2l^2 - 1))

function family1!(lines)
    for lam in (Q(-3), Q(5, 2), Q(7, 3))
        c, I = residue1(lam)
        @assert all(!iszero, c) && !(lam in (0, 1))
        @assert I == closed_form(lam) && !iszero(I)
        push!(lines, "family I at lambda = $(fr(lam)): sum u_k = 0, c = ($(join(fr.(c), ", "))), I = $(fr(I)), equal to the closed formula")
    end
end

lines = String[]
characters!(lines); parity!(lines); families!(lines)
"--common" in ARGS || family1!(lines)
foreach(println, lines)
println("$(length(lines)) lines, all checks passed")
