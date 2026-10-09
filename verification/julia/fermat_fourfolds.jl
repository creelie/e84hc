# Hodge characters of Fermat surfaces and fourfolds of degree prime to 6.
#
# For every m prime to 6 with 5 <= m <= M (M from the command line, default 55)
# list, by exhaustive search, the multisets of four and of six nonzero residues
# mod m with sum zero whose representatives in [0, m) add up to 2m (four
# entries) or 3m (six entries) after multiplication by every unit t.  These are
# the Hodge characters of the Fermat surface and fourfold of degree m.  Check
# the classification proved in the paper: every such quadruple contains a pair
# a, -a, and every such sextuple contains a pair or is 5-standard,
# {x, x + m/5, ..., x + 4m/5, -5x}.
#
# The output is line for line the same as that of c/fermat_fourfolds.c and
# python/fermat_fourfolds.py.

balanced(a, m, units, h) = all(t -> sum(mod(t * x, m) for x in a) == h, units)

function has_pair(a, m)
    n = length(a)
    any(mod(a[i] + a[k], m) == 0 for i in 1:n for k in i+1:n)
end

function standard5(a, m)
    m % 5 == 0 || return false
    for i in 1:6
        r = [a[j] for j in 1:6 if j != i]
        if length(unique(r)) == 5 && all(mod(5y - 5r[1], m) == 0 for y in r) &&
           mod(a[i] + 5r[1], m) == 0
            return true
        end
    end
    false
end

function main(M)
    bad = false
    for m in 5:M
        (m % 2 == 0 || m % 3 == 0) && continue
        units = [t for t in 1:m-1 if gcd(t, m) == 1]
        q = qn = s = sn = ss = 0
        for a0 in 1:m-1, a1 in a0:m-1, a2 in a1:m-1
            a3 = mod(3m - a0 - a1 - a2, m)
            if a3 >= a2 && a0 + a1 + a2 + a3 == 2m
                a = (a0, a1, a2, a3)
                if balanced(a, m, units, 2m)
                    q += 1
                    if !has_pair(a, m)
                        qn += 1; bad = true
                    end
                end
            end
            for a3 in a2:m-1, a4 in a3:m-1
                t5 = a0 + a1 + a2 + a3 + a4
                a5 = mod(5m - t5, m)
                (a5 < a4 || t5 + a5 != 3m) && continue
                a = (a0, a1, a2, a3, a4, a5)
                balanced(a, m, units, 3m) || continue
                s += 1
                if !has_pair(a, m)
                    sn += 1
                    if standard5(collect(a), m)
                        ss += 1
                    else
                        bad = true
                    end
                end
            end
        end
        println("H $m quadruples $q without_pair $qn sextuples $s without_pair $sn 5-standard $ss")
    end
    if bad
        println("COUNTEREXAMPLE FOUND")
        exit(1)
    end
    println("all Hodge quadruples have a pair; all Hodge sextuples have a pair or are 5-standard")
end

main(length(ARGS) > 0 ? parse(Int, ARGS[1]) : 55)
