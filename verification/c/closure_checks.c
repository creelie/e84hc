/* Exact checks of the finite steps of paper/main.tex, in C99.
 *
 * Prints the same lines "<item> <key> <value>" as
 * verification/python/closure_checks.py; verification/shell/run_all.sh
 * compares the outputs.  Nothing here is used in a proof.
 *
 * Build: cc -std=c99 -O2 -Wall -Wextra -o closure_checks closure_checks.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int nlines = 0;

#define CHECK(c)                                                         \
    do {                                                                 \
        if (!(c)) {                                                      \
            fprintf(stderr, "check failed at line %d: %s\n", __LINE__, #c); \
            exit(1);                                                     \
        }                                                                \
    } while (0)

static void emit_s(const char *item, const char *key, const char *value)
{
    printf("%s %s %s\n", item, key, value);
    nlines++;
}

static void emit_l(const char *item, const char *key, long value)
{
    printf("%s %s %ld\n", item, key, value);
    nlines++;
}

static int gcd(int a, int b)
{
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a < 0 ? -a : a;
}

static int md(long a, int m)
{
    long r = a % m;
    return (int)(r < 0 ? r + m : r);
}

static long ipow(long b, int e)
{
    long r = 1;
    while (e-- > 0)
        r *= b;
    return r;
}

/* ------------------------------------------------------------ F: Fermat */

#define MAXK 6

static int bracket(const int *a, int k, int m)
{
    long s = 0;
    for (int i = 0; i < k; i++)
        s += md(a[i], m);
    CHECK(s % m == 0);
    return (int)(s / m);
}

static int pair_type(const int *a, int k, int m)
{
    if (k == 0)
        return 1;
    int x = a[0];
    for (int j = 1; j < k; j++) {
        if (md(x + a[j], m) == 0) {
            int rest[MAXK], r = 0;
            for (int i = 1; i < k; i++)
                if (i != j)
                    rest[r++] = a[i];
            if (pair_type(rest, r, m))
                return 1;
        }
    }
    return 0;
}

struct fermat_result {
    long b_prim, h_mid, hodge, pairs;
};

static struct fermat_result fermat(int n, int m)
{
    struct fermat_result res = {0, 0, 0, 0};
    int k = n + 2, mid = (n + 2) / 2;
    int a[MAXK], b[MAXK];
    int units[64], nu = 0;
    for (int t = 1; t < m; t++)
        if (gcd(t, m) == 1)
            units[nu++] = t;
    for (int i = 0; i < k - 1; i++)
        a[i] = 1;
    for (;;) {
        long s = 0;
        for (int i = 0; i < k - 1; i++)
            s += a[i];
        int last = md(-s, m);
        if (last != 0) {
            a[k - 1] = last;
            res.b_prim++;
            if (bracket(a, k, m) == mid)
                res.h_mid++;
            int hodge = 1;
            for (int u = 0; u < nu; u++) {
                for (int i = 0; i < k; i++)
                    b[i] = md((long)units[u] * a[i], m);
                int x = bracket(b, k, m);
                for (int i = 0; i < k; i++)
                    b[i] = md(-(long)units[u] * a[i], m);
                CHECK(x + bracket(b, k, m) == n + 2);
                if (x != mid)
                    hodge = 0;
            }
            if (hodge) {
                res.hodge++;
                if (pair_type(a, k, m))
                    res.pairs++;
            }
        }
        int i = k - 2;
        while (i >= 0 && a[i] == m - 1) {
            a[i] = 1;
            i--;
        }
        if (i < 0)
            break;
        a[i]++;
    }
    return res;
}

static void check_fermat(void)
{
    int cases[2][2] = {{2, 12}, {4, 8}};
    char key[64];
    for (int c = 0; c < 2; c++) {
        int n = cases[c][0], mmax = cases[c][1];
        for (int m = 2; m <= mmax; m++) {
            struct fermat_result r = fermat(n, m);
            long closed = (ipow(m - 1, n + 2) + (n % 2 ? -1 : 1) * (m - 1)) / m;
            CHECK(r.b_prim == closed);
            snprintf(key, sizeof key, "n=%d,m=%d,b_prim", n, m);
            emit_l("F", key, r.b_prim);
            snprintf(key, sizeof key, "n=%d,m=%d,h_mid_prim", n, m);
            emit_l("F", key, r.h_mid);
            snprintf(key, sizeof key, "n=%d,m=%d,hodge_prim", n, m);
            emit_l("F", key, r.hodge);
            snprintf(key, sizeof key, "n=%d,m=%d,pair_type", n, m);
            emit_l("F", key, r.pairs);
            if (n == 2) {
                long rho = r.hodge + 1, h11 = r.h_mid + 1;
                CHECK(3 * h11 == 2L * m * m * m - 6L * m * m + 7L * m);
                snprintf(key, sizeof key, "n=2,m=%d,rho", m);
                emit_l("F", key, rho);
                if (gcd(m, 6) == 1) {
                    CHECK(rho == 3L * (m - 1) * (m - 2) + 1);
                    CHECK(r.pairs == r.hodge);
                }
            }
        }
    }
    CHECK(fermat(2, 4).hodge + 1 == 20);
    CHECK(fermat(2, 5).hodge + 1 == 37);
    CHECK(fermat(2, 6).hodge + 1 == 86);
    emit_s("F", "aoki_shioda_values", "20,37,86");
}

/* --------------------------------------------------- J: Fermat curves */

static void check_fermat_curves(void)
{
    int worst = 0;
    char key[64];
    for (int m = 3; m <= 30; m++) {
        int units[64], nu = 0;
        for (int t = 1; t < m; t++)
            if (gcd(t, m) == 1)
                units[nu++] = t;
        /* characters (a0, a1, a2) with ai != 0 and sum 0, indexed by a0, a1 */
        static int seen[32][32];
        memset(seen, 0, sizeof seen);
        int nchars = 0, orbits = 0;
        for (int a0 = 1; a0 < m; a0++)
            for (int a1 = 1; a1 < m; a1++) {
                if (md(-(a0 + a1), m) == 0)
                    continue;
                nchars++;
                if (seen[a0][a1])
                    continue;
                orbits++;
                int size = 0, hol = 0;
                for (int u = 0; u < nu; u++) {
                    int b[3] = {md((long)units[u] * a0, m), md((long)units[u] * a1, m), 0};
                    b[2] = md(-(b[0] + b[1]), m);
                    if (seen[b[0]][b[1]])
                        continue;
                    seen[b[0]][b[1]] = 1;
                    size++;
                    int x = bracket(b, 3, m);
                    CHECK(x == 1 || x == 2);
                    int nb[3] = {md(-b[0], m), md(-b[1], m), md(-b[2], m)};
                    CHECK((x == 1) != (bracket(nb, 3, m) == 1));
                    if (x == 1)
                        hol++;
                }
                CHECK(2 * hol == size);
                if (size > worst)
                    worst = size;
            }
        CHECK(nchars == (m - 1) * (m - 2));
        snprintf(key, sizeof key, "m=%d,orbits", m);
        emit_l("J", key, orbits);
    }
    emit_l("J", "largest_orbit_up_to_30", worst);
}

/* -------------------------------------------------- S: the switch lemma */

/* a list of p rows of s signs is stored as an int array x[i*3 + c] */
static int switch_steps(const int *x0, const int *y, int p, int s)
{
    int x[12], prev[12];
    memcpy(x, x0, sizeof x);
    int steps = 0;
    for (int col = 0; col < s; col++) {
        int plus[4], minus[4], np = 0, nm = 0;
        for (int i = 0; i < p; i++) {
            if (x[i * 3 + col] == 1 && y[i * 3 + col] == -1)
                plus[np++] = i;
            if (x[i * 3 + col] == -1 && y[i * 3 + col] == 1)
                minus[nm++] = i;
        }
        CHECK(np == nm);
        for (int t = 0; t < np; t++) {
            memcpy(prev, x, sizeof x);
            int i = plus[t], j = minus[t];
            int tmp = x[i * 3 + col];
            x[i * 3 + col] = x[j * 3 + col];
            x[j * 3 + col] = tmp;
            steps++;
            int changed[4], nc = 0;
            for (int r = 0; r < p; r++) {
                int diff = 0;
                for (int c = 0; c < s; c++)
                    if (prev[r * 3 + c] != x[r * 3 + c])
                        diff = 1;
                if (diff)
                    changed[nc++] = r;
            }
            CHECK(nc == 2);
            for (int c = 0; c < s; c++)
                CHECK(prev[changed[0] * 3 + c] + prev[changed[1] * 3 + c] ==
                      x[changed[0] * 3 + c] + x[changed[1] * 3 + c]);
        }
    }
    for (int i = 0; i < p; i++)
        for (int c = 0; c < s; c++)
            CHECK(x[i * 3 + c] == y[i * 3 + c]);
    return steps;
}

static void decode(long code, int p, int s, int *x)
{
    memset(x, 0, 12 * sizeof(int));
    for (int i = 0; i < p; i++)
        for (int c = 0; c < s; c++) {
            x[i * 3 + c] = (code & 1) ? -1 : 1;
            code >>= 1;
        }
}

static void check_switch(void)
{
    long total = 0;
    char key[64];
    for (int p = 1; p <= 4; p++)
        for (int s = 1; s <= 3; s++) {
            long nlists = 1L << (p * s);
            long pairs = 0;
            int maxsteps = 0;
            int x[12], y[12];
            for (long cx = 0; cx < nlists; cx++)
                for (long cy = 0; cy < nlists; cy++) {
                    decode(cx, p, s, x);
                    decode(cy, p, s, y);
                    int same = 1;
                    for (int c = 0; c < s; c++) {
                        int sx = 0, sy = 0;
                        for (int i = 0; i < p; i++) {
                            sx += x[i * 3 + c];
                            sy += y[i * 3 + c];
                        }
                        if (sx != sy)
                            same = 0;
                    }
                    if (!same)
                        continue;
                    int st = switch_steps(x, y, p, s);
                    pairs++;
                    if (st > maxsteps)
                        maxsteps = st;
                }
            CHECK(maxsteps <= s * (p / 2));
            total += pairs;
            snprintf(key, sizeof key, "p=%d,s=%d,pairs", p, s);
            emit_l("S", key, pairs);
            snprintf(key, sizeof key, "p=%d,s=%d,max_switches", p, s);
            emit_l("S", key, maxsteps);
        }
    emit_l("S", "all_pairs", total);
}

/* ------------------------------------------------------------ G: signs */

static int perm_sign(const int *perm, int n)
{
    int sign = 1;
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (perm[i] > perm[j])
                sign = -sign;
    return sign;
}

static void check_signs(void)
{
    int t[32];
    char key[64];
    for (int p = 1; p <= 10; p++) {
        for (int i = 0; i < p; i++) {
            t[2 * i] = i;
            t[2 * i + 1] = p + i;
        }
        int sg = perm_sign(t, 2 * p);
        CHECK(sg == ((p * (p - 1) / 2) % 2 ? -1 : 1));
        snprintf(key, sizeof key, "regroup_p=%d", p);
        emit_l("G", key, sg);
    }
    for (int k = 1; k <= 8; k++) {
        for (int i = 0; i < k; i++) {
            t[2 * i] = i;
            t[2 * i + 1] = k + i;
        }
        int sg = perm_sign(t, 2 * k);
        CHECK(sg == ((k * (k - 1) / 2) % 2 ? -1 : 1));
        snprintf(key, sizeof key, "kernel_k=%d", k);
        emit_l("G", key, sg);
    }
}

/* ---------------------------------------------------- W: Weil families */

static void check_weil(void)
{
    char key[64], val[128];
    for (int n = 2; n <= 12; n++) {
        snprintf(key, sizeof key, "n=%d,prym,weil", n);
        snprintf(val, sizeof val, "%d,%d", 3 * n, n * n);
        emit_s("W", key, val);
    }
    for (int m = 2; m <= 12; m++) {
        val[0] = 0;
        for (int k = 0; k <= 12; k++)
            if (3 * (m + k) + 3 * k >= (m + k) * (m + k)) {
                char b[8];
                snprintf(b, sizeof b, val[0] ? ",%d" : "%d", k);
                strcat(val, b);
            }
        snprintf(key, sizeof key, "m=%d,k_passing", m);
        emit_s("W", key, val[0] ? val : "none");
    }
    for (int m = 4; m < 60; m++)
        for (int k = 0; k < 200; k++)
            CHECK(3 * (m + k) + 3 * k < (m + k) * (m + k));
}

/* --------------------------------------------- L: the logical skeleton */

/* the order of the names is the order of OPEN in the Python version */
enum { F2, F3P, L_, M_, V_, IP, CM, SR, HC, FER, W3, NATOMS };
static const char *NAME[NATOMS] = {"F2", "F3P", "L", "M", "V", "IP", "CM",
                                   "SR", "HC", "FER", "W3"};
#define B(a) (1u << (a))
static const int OPENS[] = {F2, F3P, L_, M_, V_, IP, CM, SR};
#define NOPEN 8
static const int OPENS_NO_CM[] = {F2, F3P, L_, M_, V_, IP, SR};
static const struct { unsigned prem; int concl; } RULES[] = {
    {B(F2) | B(F3P), HC},
    {B(HC), F2}, {B(HC), F3P},
    {B(HC), L_}, {B(HC), M_}, {B(HC), V_},
    {B(L_) | B(M_), HC},
    {B(L_), F2},
    {B(V_), F2},
    {B(V_), IP},
    {B(F3P), M_},
    {B(CM) | B(IP), F2},
    {B(F2), IP}, {B(F2), CM},
    {B(CM), FER}, {B(HC), FER},
    {B(SR), W3}, {B(F2), W3},
};
#define NRULES (sizeof RULES / sizeof RULES[0])

static unsigned closure(unsigned have)
{
    int changed = 1;
    while (changed) {
        changed = 0;
        for (size_t r = 0; r < NRULES; r++)
            if (!(have & B(RULES[r].concl)) && (have & RULES[r].prem) == RULES[r].prem) {
                have |= B(RULES[r].concl);
                changed = 1;
            }
    }
    return have;
}

static int is_closed(unsigned T)
{
    for (size_t r = 0; r < NRULES; r++)
        if ((T & RULES[r].prem) == RULES[r].prem && !(T & B(RULES[r].concl)))
            return 0;
    return 1;
}

static void join(unsigned set, const char *sep, char *buf, size_t n)
{
    buf[0] = 0;
    for (int a = 0; a < NATOMS; a++)
        if (set & B(a)) {
            if (buf[0])
                strncat(buf, sep, n - strlen(buf) - 1);
            strncat(buf, NAME[a], n - strlen(buf) - 1);
        }
}

/* minimal sets in the order of itertools.combinations over pool */
static int minimal_sets(unsigned base, const int *pool, int npool, unsigned *found)
{
    int nf = 0;
    for (int r = 1; r <= npool; r++) {
        int idx[NOPEN];
        for (int i = 0; i < r; i++)
            idx[i] = i;
        for (;;) {
            unsigned S = 0;
            for (int i = 0; i < r; i++)
                S |= B(pool[idx[i]]);
            int sub = 0;
            for (int f = 0; f < nf; f++)
                if ((found[f] & S) == found[f])
                    sub = 1;
            if (!sub && (closure(base | S) & B(HC)))
                found[nf++] = S;
            int i = r - 1;
            while (i >= 0 && idx[i] == npool - r + i)
                i--;
            if (i < 0)
                break;
            idx[i]++;
            for (int j = i + 1; j < r; j++)
                idx[j] = idx[j - 1] + 1;
        }
    }
    return nf;
}

static void check_logic(void)
{
    char buf[256];
    unsigned all = (1u << NATOMS) - 1;
    unsigned cl = closure(B(CM));
    CHECK(cl == (B(CM) | B(FER)));
    join(cl & ~B(CM), ",", buf, sizeof buf);
    emit_s("L", "closure_of_CM", buf);
    for (size_t r = 0; r < NRULES; r++)
        CHECK((cl & RULES[r].prem) != RULES[r].prem || (cl & B(RULES[r].concl)));
    emit_s("L", "countermodel_HC", (cl & B(HC)) ? "true" : "false");
    /* the four closed sets of the proof of Theorem B */
    static const struct { unsigned out; const char *name; } CL[] = {
        {B(HC) | B(M_) | B(F3P), "M+F3P"},
        {B(HC) | B(L_) | B(F3P), "L+F3P"},
        {B(HC) | B(F2) | B(L_) | B(V_) | B(IP), "F2+L+V+IP"},
        {B(HC) | B(F2) | B(L_) | B(V_) | B(CM), "F2+L+V+CM"},
    };
    for (int c = 0; c < 4; c++) {
        unsigned T = all & ~CL[c].out;
        CHECK(is_closed(T) && !(T & B(HC)));
        emit_s("L", "closed_without", CL[c].name);
    }
    CHECK(!(closure(B(SR) | B(CM)) & B(HC)));
    unsigned found[64], found2[64];
    int nf = minimal_sets(0, OPENS, NOPEN, found);
    for (int f = 0; f < nf; f++) {
        join(found[f], "+", buf, sizeof buf);
        emit_s("L", "minimal_set", buf);
    }
    emit_l("L", "minimal_sets", nf);
    int nf2 = minimal_sets(B(CM), OPENS_NO_CM, NOPEN - 1, found2);
    for (int f = 0; f < nf2; f++) {
        join(found2[f], "+", buf, sizeof buf);
        emit_s("L", "minimal_set_given_CM", buf);
    }
    unsigned need = B(F2) | B(F3P) | B(L_) | B(M_) | B(V_) | B(IP) | B(CM);
    for (int f = 0; f < nf; f++) {
        CHECK(found[f] & (B(M_) | B(F3P)));
        CHECK((closure(found[f]) & need) == need);
    }
    unsigned avoid = B(F2) | B(F3P) | B(IP) | B(CM) | B(SR);
    int nb = 0;
    for (int f = 0; f < nf; f++)
        if (!(found[f] & avoid)) {
            join(found[f], "+", buf, sizeof buf);
            emit_s("L", "bypass_F2_F3P_SR", buf);
            CHECK(found[f] == (B(L_) | B(M_)));
            nb++;
        }
    CHECK(nb == 1);
}

int main(void)
{
    check_fermat();
    check_fermat_curves();
    check_switch();
    check_signs();
    check_weil();
    check_logic();
    printf("\n%d lines, all checks passed\n", nlines);
    return 0;
}
