# Exact checks of the finite steps of paper/main.tex, in Julia.
#
# The output is the same list of lines "<item> <key> <value>" that
# verification/python/closure_checks.py prints, and
# verification/shell/run_all.sh compares the two (and the C version) line by
# line.  Nothing here is used in a proof.

const OUT = String[]

function emit(item, key, value)
    line = "$item $key $value"
    push!(OUT, line)
    println(line)
end

units(m) = [t for t in 1:m-1 if gcd(t, m) == 1]

# ---------------------------------------------------------------- F: Fermat

function characters(n, m)
    k = n + 2
    out = Vector{Vector{Int}}()
    for a in Iterators.product(ntuple(_ -> 1:m-1, k - 1)...)
        last = mod(-sum(a), m)
        last != 0 && push!(out, [a..., last])
    end
    out
end

function bracket(a, m)
    s = sum(mod(x, m) for x in a)
    @assert s % m == 0
    s ÷ m
end

function pair_type(a, m)
    isempty(a) && return true
    x = a[1]
    for j in 2:length(a)
        if mod(x + a[j], m) == 0
            rest = vcat(a[2:j-1], a[j+1:end])
            pair_type(rest, m) && return true
        end
    end
    false
end

function fermat(n, m)
    chars = characters(n, m)
    U = units(m)
    mid = (n + 2) ÷ 2
    b_prim = length(chars)
    h_mid = count(a -> bracket(a, m) == mid, chars)
    hodge = [a for a in chars if all(bracket(mod.(t .* a, m), m) == mid for t in U)]
    odd_ok = all(bracket(mod.(t .* a, m), m) + bracket(mod.(-t .* a, m), m) == n + 2
                 for a in chars for t in U)
    pairs = count(a -> pair_type(a, m), hodge)
    b_prim, h_mid, length(hodge), pairs, odd_ok
end

function check_fermat()
    for (n, mmax) in ((2, 12), (4, 8))
        for m in 2:mmax
            b_prim, h_mid, hdg, pairs, odd_ok = fermat(n, m)
            closed = ((m - 1)^(n + 2) + (-1)^n * (m - 1)) ÷ m
            @assert b_prim == closed
            @assert odd_ok
            emit("F", "n=$n,m=$m,b_prim", b_prim)
            emit("F", "n=$n,m=$m,h_mid_prim", h_mid)
            emit("F", "n=$n,m=$m,hodge_prim", hdg)
            emit("F", "n=$n,m=$m,pair_type", pairs)
            if n == 2
                rho = hdg + 1
                h11 = h_mid + 1
                @assert 3 * h11 == 2m^3 - 6m^2 + 7m
                emit("F", "n=2,m=$m,rho", rho)
                if gcd(m, 6) == 1
                    @assert rho == 3 * (m - 1) * (m - 2) + 1
                    @assert pairs == hdg
                end
            end
        end
    end
    @assert fermat(2, 4)[3] + 1 == 20
    @assert fermat(2, 5)[3] + 1 == 37
    @assert fermat(2, 6)[3] + 1 == 86
    emit("F", "aoki_shioda_values", "20,37,86")
end

# ------------------------------------------------------- J: Fermat curves

function check_fermat_curves()
    worst = 0
    for m in 3:30
        U = units(m)
        chars = characters(1, m)
        seen = Set{Vector{Int}}()
        orbits = 0
        for a in chars
            a in seen && continue
            orb = Set(mod.(t .* a, m) for t in U)
            union!(seen, orb)
            orbits += 1
            hol = count(b -> bracket(b, m) == 1, orb)
            @assert all(bracket(b, m) in (1, 2) for b in orb)
            for b in orb
                nb = mod.(-b, m)
                @assert (bracket(b, m) == 1) != (bracket(nb, m) == 1)
            end
            @assert 2hol == length(orb)
            worst = max(worst, length(orb))
        end
        genus = (m - 1) * (m - 2) ÷ 2
        @assert length(chars) == 2genus
        emit("J", "m=$m,orbits", orbits)
    end
    emit("J", "largest_orbit_up_to_30", worst)
end

# ------------------------------------------------------ S: the switch lemma

function switch_sequence(x, y)
    x = [copy(r) for r in x]
    p = length(x)
    s = p > 0 ? length(x[1]) : 0
    seq = [deepcopy(x)]
    for col in 1:s
        plus = [i for i in 1:p if x[i][col] == 1 && y[i][col] == -1]
        minus = [i for i in 1:p if x[i][col] == -1 && y[i][col] == 1]
        @assert length(plus) == length(minus)
        for (i, j) in zip(plus, minus)
            x[i][col], x[j][col] = x[j][col], x[i][col]
            push!(seq, deepcopy(x))
        end
    end
    @assert x == y
    seq
end

function check_switch()
    total_pairs = 0
    for p in 1:4, s in 1:3
        rows = [collect(r) for r in Iterators.product(ntuple(_ -> (1, -1), s)...)]
        bysum = Dict{Vector{Int},Vector{Vector{Vector{Int}}}}()
        for L in Iterators.product(ntuple(_ -> rows, p)...)
            Lv = [copy(r) for r in L]
            key = [sum(r[c] for r in Lv) for c in 1:s]
            push!(get!(bysum, key, Vector{Vector{Vector{Int}}}()), Lv)
        end
        pairs = 0
        maxsteps = 0
        for group in values(bysum), x in group, y in group
            seq = switch_sequence(x, y)
            for (u, v) in zip(seq, seq[2:end])
                changed = [i for i in 1:p if u[i] != v[i]]
                @assert length(changed) == 2
                i, j = changed
                for c in 1:s
                    @assert u[i][c] + u[j][c] == v[i][c] + v[j][c]
                end
            end
            pairs += 1
            maxsteps = max(maxsteps, length(seq) - 1)
        end
        @assert maxsteps <= s * (p ÷ 2)
        total_pairs += pairs
        emit("S", "p=$p,s=$s,pairs", pairs)
        emit("S", "p=$p,s=$s,max_switches", maxsteps)
    end
    emit("S", "all_pairs", total_pairs)
end

# ----------------------------------------------------------------- G: signs

function perm_sign(perm)
    sign = 1
    for i in eachindex(perm), j in i+1:length(perm)
        perm[i] > perm[j] && (sign = -sign)
    end
    sign
end

function check_signs()
    for p in 1:10
        target = Int[]
        for i in 0:p-1
            append!(target, (i, p + i))
        end
        sgn = perm_sign(target)
        @assert sgn == (-1)^(p * (p - 1) ÷ 2)
        emit("G", "regroup_p=$p", sgn)
    end
    for k in 1:8
        order = Int[]
        for i in 0:k-1
            append!(order, (i, k + i))
        end
        sgn = perm_sign(order)
        @assert sgn == (-1)^(k * (k - 1) ÷ 2)
        emit("G", "kernel_k=$k", sgn)
    end
end

# ------------------------------------------------------- W: Weil families

function check_weil()
    for n in 2:12
        emit("W", "n=$n,prym,weil", "$(3n),$(n*n)")
    end
    for m in 2:12
        ks = [k for k in 0:12 if 3 * (m + k) + 3k >= (m + k)^2]
        emit("W", "m=$m,k_passing", isempty(ks) ? "none" : join(ks, ","))
    end
    @assert [k for k in 0:12 if 3 * (2 + k) + 3k >= (2 + k)^2] == [0, 1, 2]
    @assert [k for k in 0:12 if 3 * (3 + k) + 3k >= (3 + k)^2] == [0]
    for m in 4:59
        @assert all(3 * (m + k) + 3k < (m + k)^2 for k in 0:199)
    end
    # Proposition 5.15: cyclic triple covers of a genus-q curve branched at r
    # points with Prym of dimension 2n; their families have dimension q+2n-1.
    for n in 2:12
        best = (-1, -1, -1)
        for q in 0:(n + 1)
            r = 2n + 2 - 2q
            @assert r >= 0 && r != 1
            @assert 2 * (3q - 2 + r) - 2 == 3 * (2q - 2) + 2r
            @assert (3q - 2 + r) - q == 2n
            d = q == 0 ? r - 3 : (q == 1 ? r : 3q - 3 + r)
            @assert d == q + 2n - 1
            if d > best[1]
                best = (d, q, r)
            elseif d == best[1]
                best = (d, -1, -1)
            end
        end
        @assert best == (3n, n + 1, 0)
        emit("W", "n=$n,cyclic_max", "$(best[1]),$(best[2]),$(best[3])")
    end
end

# ------------------------------------------------- L: the logical skeleton

const OPEN = ["F2", "F3P", "L", "M", "V", "IP", "CM", "SR"]
const DERIVED = ["HC", "FER", "W3"]
const ATOMS = vcat(OPEN, DERIVED)
const RULES = [
    (["F2", "F3P"], "HC"),
    (["HC"], "F2"), (["HC"], "F3P"),
    (["HC"], "L"), (["HC"], "M"), (["HC"], "V"),
    (["L", "M"], "HC"),
    (["L"], "F2"),
    (["V"], "F2"),
    (["V"], "IP"),
    (["F3P"], "M"),
    (["CM", "IP"], "F2"),
    (["F2"], "IP"), (["F2"], "CM"),
    (["CM"], "FER"), (["HC"], "FER"),
    (["SR"], "W3"), (["F2"], "W3"),
]
const CLOSED_COMPLEMENTS = [
    ["HC", "M", "F3P"],
    ["HC", "L", "F3P"],
    ["HC", "F2", "L", "V", "IP"],
    ["HC", "F2", "L", "V", "CM"],
]

function closure(start)
    have = Set(start)
    changed = true
    while changed
        changed = false
        for (prem, concl) in RULES
            if !(concl in have) && all(p in have for p in prem)
                push!(have, concl)
                changed = true
            end
        end
    end
    have
end

# subsets of v of size r, in the order of Python's itertools.combinations
function combos(v, r)
    out = Vector{Vector{String}}()
    n = length(v)
    idx = collect(1:r)
    r > n && return out
    while true
        push!(out, v[idx])
        i = r
        while i >= 1 && idx[i] == n - r + i
            i -= 1
        end
        i == 0 && break
        idx[i] += 1
        for j in i+1:r
            idx[j] = idx[j-1] + 1
        end
    end
    out
end

function minimal_sets(base, pool)
    found = Vector{Vector{String}}()
    for r in 1:length(pool), S in combos(pool, r)
        any(issubset(M, S) for M in found) && continue
        "HC" in closure(union(base, S)) && push!(found, S)
    end
    found
end

is_closed(T) = all(concl in T for (prem, concl) in RULES if all(p in T for p in prem))

function check_logic()
    cl = closure(["CM"])
    @assert cl == Set(["CM", "FER"])
    emit("L", "closure_of_CM", join(sort(collect(setdiff(cl, ["CM"]))), ","))
    val = Dict(a => (a in cl) for a in ATOMS)
    for (prem, concl) in RULES
        @assert !all(val[p] for p in prem) || val[concl]
    end
    emit("L", "countermodel_HC", string(val["HC"]))
    for out in CLOSED_COMPLEMENTS
        T = setdiff(ATOMS, out)
        @assert is_closed(T) && !("HC" in T)
        emit("L", "closed_without", join(out[2:end], "+"))
    end
    @assert !("HC" in closure(["SR", "CM"]))
    mins = minimal_sets(String[], OPEN)
    for S in mins
        emit("L", "minimal_set", join(S, "+"))
    end
    emit("L", "minimal_sets", length(mins))
    mins_cm = minimal_sets(["CM"], [a for a in OPEN if a != "CM"])
    for S in mins_cm
        emit("L", "minimal_set_given_CM", join(S, "+"))
    end
    for S in mins
        @assert "M" in S || "F3P" in S
        @assert issubset(setdiff(OPEN, ["SR"]), closure(S))
    end
    avoid = ["F2", "F3P", "IP", "CM", "SR"]
    bypass = [S for S in mins if isempty(intersect(avoid, S))]
    for S in bypass
        emit("L", "bypass_F2_F3P_SR", join(S, "+"))
    end
    @assert bypass == [["L", "M"]]
end

function main()
    check_fermat()
    check_fermat_curves()
    check_switch()
    check_signs()
    check_weil()
    check_logic()
    println()
    println("$(length(OUT)) lines, all checks passed")
end

main()
