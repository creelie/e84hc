# Hodge characters of Fermat fourfolds of odd degree divisible by 3.
#
# For every odd m divisible by 3 with 3 <= m <= M (M from the command line,
# default 45) list, by exhaustive search, the balanced sextuples: multisets of
# six nonzero residues mod m whose representatives in [0, m) add up to 3m after
# multiplication by every unit t.  For each one that contains no pair a, -a and
# generates Z/m, look for a direct or a lowering move (Definition "def:move" of
# the paper); if there is none, check that tA is one of O21, O33, O39 for some
# unit t (Theorem "thm:moves").  Then check the identities of Lemma
# "lem:exceptional" and that the exceptional sets have no move.
#
# The output is line for line the same as that of c/fermat_odd.c and
# python/fermat_odd.py.

const EXCEPTIONAL = Dict(21 => [1, 4, 9, 15, 16, 18], 33 => [1, 4, 16, 22, 25, 31],
                         39 => [1, 7, 16, 22, 34, 37])

units(m) = [t for t in 1:m-1 if gcd(t, m) == 1]

function balanced(a, m)
    h = length(a) * m ÷ 2
    mod(sum(a), m) == 0 && all(t -> sum(mod(t * x, m) for x in a) == h, units(m))
end

function has_pair(a, m)
    n = length(a)
    any(mod(a[i] + a[k], m) == 0 for i in 1:n for k in i+1:n)
end

isprime_(p) = p >= 2 && all(p % q != 0 for q in 2:p-1)
odd_primes(m) = [p for p in 3:2:m if m % p == 0 && isprime_(p)]
profile(a, m) = sort([m ÷ gcd(x, m) for x in a], rev = true)

function move(a, m, want)
    prof = profile(a, m)
    for l in odd_primes(m)
        d = m ÷ l
        for x in 0:d-1
            mod(l * x, m) == 0 && continue
            fib = [mod(x + j * d, m) for j in 0:l-1]
            s = [y for y in fib if y in a]
            size = 7 + l - 2 * length(s)
            want == :direct && size <= 4 && return true
            if want == :lowering && size == 6
                b = copy(a)
                for y in s
                    deleteat!(b, findfirst(==(y), b))
                end
                append!(b, [mod(-y, m) for y in fib if !(y in s)])
                push!(b, mod(l * x, m))
                profile(b, m) < prof && return true
            end
        end
    end
    false
end

function exceptional(a, m)
    haskey(EXCEPTIONAL, m) || return false
    any(sort([mod(t * x, m) for x in a]) == EXCEPTIONAL[m] for t in units(m))
end

function generates(a, m)
    g = m
    for x in a
        g = gcd(g, x)
    end
    g == 1
end

function census(M)
    bad = false
    for m in 3:6:M
        s = np = gen = dm = lm = ex = 0
        for a0 in 1:m-1, a1 in a0:m-1, a2 in a1:m-1, a3 in a2:m-1, a4 in a3:m-1
            a5 = 3m - a0 - a1 - a2 - a3 - a4
            (a5 < a4 || a5 >= m) && continue
            a = [a0, a1, a2, a3, a4, a5]
            balanced(a, m) || continue
            s += 1
            has_pair(a, m) && continue
            np += 1
            generates(a, m) || continue
            gen += 1
            if move(a, m, :direct)
                dm += 1
            elseif move(a, m, :lowering)
                lm += 1
            elseif exceptional(a, m)
                ex += 1
            else
                bad = true
                println("NO MOVE AND NOT EXCEPTIONAL: m=$m [", join(a, ", "), "]")
            end
        end
        println("H $m sextuples $s without_pair $np generating $gen direct $dm lowering $lm exceptional $ex")
    end
    bad
end

msum(parts...) = sort(vcat(parts...))
yn(ok) = ok ? "yes" : "NO"

function identities()
    bad = false
    for m in (21, 33, 39)
        o = EXCEPTIONAL[m]
        ok = balanced(o, m) && !has_pair(o, m) && generates(o, m) &&
             !move(o, m, :direct) && !move(o, m, :lowering)
        println("O$m balanced, without pair, generating, no move: ", yn(ok))
        bad |= !ok
    end
    sig = [2, 9, 16, 15]
    q = [1, 4, 18, 19]
    ok = msum(EXCEPTIONAL[21], [2, 19]) == msum(sig, q) && balanced(sig, 21) && balanced(q, 21)
    println("O21 + {2,19} = sigma(3,2) + Q, all parts balanced: ", yn(ok))
    bad |= !ok
    for (m, x1, x2, pairs, q) in ((33, 32, 8, [1, 65, 25, 41], [1, 25, 44, 62]),
                                  (39, 32, 5, [5, 73, 7, 71], [2, 7, 73, 74]))
        M = 2m
        T(x) = [x, mod(x + m, M), mod(-2x, M), m]
        a = [2y for y in EXCEPTIONAL[m]]
        ok = msum(a, pairs, [m, m]) == msum(q, T(x1), T(x2)) && balanced(a, M) &&
             balanced(q, M) && balanced(T(x1), M) && balanced(T(x2), M)
        println("2*O$m + pairs + {$m,$m} = Q + T($x1) + T($x2) at level $M, all parts balanced: ", yn(ok))
        bad |= !ok
    end
    ok = all(balanced([x, mod(x + M ÷ 2, M), mod(-2x, M), M ÷ 2], M)
             for M in 4:2:200 for x in 1:M-1 if mod(2x, M) != 0)
    println("T(x) = {x, x+M/2, -2x, M/2} balanced for all even M <= 200: ", yn(ok))
    bad |= !ok
    bad
end

function main()
    M = length(ARGS) > 0 ? parse(Int, ARGS[1]) : 45
    bad = census(M)
    bad |= identities()
    if bad
        println("FAILURE")
        exit(1)
    end
    println("every generating Hodge sextuple without a pair has a move or is exceptional")
end

main()
