/* Hodge characters of Fermat fourfolds of odd degree divisible by 3.
 *
 * For every odd m divisible by 3 with 3 <= m <= M (M from the command line,
 * default 45) this program lists, by exhaustive search, the balanced
 * sextuples: multisets of six nonzero residues mod m whose representatives in
 * [0, m) add up to 3m after multiplication by every unit t.  For each one that
 * contains no pair a, -a and generates Z/m it looks for a direct or a lowering
 * move (Definition "def:move" of the paper); if there is none, it checks that
 * tA is one of O21, O33, O39 for some unit t (Theorem "thm:moves").  Then it
 * checks the identities of Lemma "lem:exceptional" and that the exceptional
 * sets have no move.
 *
 * The output is line for line the same as that of python/fermat_odd.py and
 * julia/fermat_odd.jl.  The program exits with status 1 if a check fails.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const int EXC[3][7] = {{21, 1, 4, 9, 15, 16, 18},
                              {33, 1, 4, 16, 22, 25, 31},
                              {39, 1, 7, 16, 22, 34, 37}};

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int md(long x, int m) { long r = x % m; return (int)(r < 0 ? r + m : r); }

static int balanced(const int *a, int n, int m) {
    long s0 = 0;
    for (int i = 0; i < n; i++) s0 += a[i];
    if (s0 % m) return 0;
    for (int t = 1; t < m; t++) {
        if (gcd(t, m) != 1) continue;
        long s = 0;
        for (int i = 0; i < n; i++) s += md((long)t * a[i], m);
        if (2 * s != (long)n * m) return 0;
    }
    return 1;
}

static int has_pair(const int *a, int n, int m) {
    for (int i = 0; i < n; i++)
        for (int k = i + 1; k < n; k++)
            if ((a[i] + a[k]) % m == 0) return 1;
    return 0;
}

static int is_prime(int p) {
    if (p < 2) return 0;
    for (int q = 2; q * q <= p; q++) if (p % q == 0) return 0;
    return 1;
}

static int cmp_desc(const void *x, const void *y) { return *(const int *)y - *(const int *)x; }
static int cmp_asc(const void *x, const void *y) { return *(const int *)x - *(const int *)y; }

static void profile(const int *a, int n, int m, int *out) {
    for (int i = 0; i < n; i++) out[i] = m / gcd(a[i], m);
    qsort(out, (size_t)n, sizeof(int), cmp_desc);
}

/* want = 0: direct move, want = 1: lowering move */
static int move(const int *a, int m, int want) {
    int prof[6];
    profile(a, 6, m, prof);
    for (int l = 3; l <= m; l += 2) {
        if (m % l || !is_prime(l)) continue;
        int d = m / l;
        for (int x = 0; x < d; x++) {
            if (md((long)l * x, m) == 0) continue;
            int fib[64], ins[64], k = 0;
            for (int j = 0; j < l; j++) {
                fib[j] = (x + j * d) % m;
                ins[j] = 0;
                for (int i = 0; i < 6; i++) if (a[i] == fib[j]) { ins[j] = 1; break; }
                k += ins[j];
            }
            int size = 7 + l - 2 * k;
            if (want == 0 && size <= 4) return 1;
            if (want == 1 && size == 6) {
                int b[6], nb = 0, removed[6] = {0};
                for (int j = 0; j < l; j++) {       /* remove one copy of each element of S */
                    if (!ins[j]) continue;
                    for (int i = 0; i < 6; i++)
                        if (!removed[i] && a[i] == fib[j]) { removed[i] = 1; break; }
                }
                for (int i = 0; i < 6; i++) if (!removed[i]) b[nb++] = a[i];
                for (int j = 0; j < l; j++) if (!ins[j]) b[nb++] = md(-(long)fib[j], m);
                b[nb++] = md((long)l * x, m);
                int pb[6];
                profile(b, 6, m, pb);
                for (int i = 0; i < 6; i++) {
                    if (pb[i] < prof[i]) return 1;
                    if (pb[i] > prof[i]) break;
                }
            }
        }
    }
    return 0;
}

static int exceptional(const int *a, int m) {
    for (int e = 0; e < 3; e++) {
        if (EXC[e][0] != m) continue;
        for (int t = 1; t < m; t++) {
            if (gcd(t, m) != 1) continue;
            int b[6];
            for (int i = 0; i < 6; i++) b[i] = md((long)t * a[i], m);
            qsort(b, 6, sizeof(int), cmp_asc);
            if (memcmp(b, &EXC[e][1], sizeof b) == 0) return 1;
        }
    }
    return 0;
}

static int generates(const int *a, int m) {
    int g = m;
    for (int i = 0; i < 6; i++) g = gcd(g, a[i]);
    return g == 1;
}

static int census(int M) {
    int bad = 0;
    for (int m = 3; m <= M; m += 6) {
        long s = 0, np = 0, gen = 0, dm = 0, lm = 0, ex = 0;
        int a[6];
        for (a[0] = 1; a[0] < m; a[0]++)
         for (a[1] = a[0]; a[1] < m; a[1]++)
          for (a[2] = a[1]; a[2] < m; a[2]++)
           for (a[3] = a[2]; a[3] < m; a[3]++)
            for (a[4] = a[3]; a[4] < m; a[4]++) {
                a[5] = 3 * m - a[0] - a[1] - a[2] - a[3] - a[4];
                if (a[5] < a[4] || a[5] >= m) continue;
                if (!balanced(a, 6, m)) continue;
                s++;
                if (has_pair(a, 6, m)) continue;
                np++;
                if (!generates(a, m)) continue;
                gen++;
                if (move(a, m, 0)) dm++;
                else if (move(a, m, 1)) lm++;
                else if (exceptional(a, m)) ex++;
                else {
                    bad = 1;
                    printf("NO MOVE AND NOT EXCEPTIONAL: m=%d [%d, %d, %d, %d, %d, %d]\n",
                           m, a[0], a[1], a[2], a[3], a[4], a[5]);
                }
            }
        printf("H %d sextuples %ld without_pair %ld generating %ld direct %ld lowering %ld exceptional %ld\n",
               m, s, np, gen, dm, lm, ex);
    }
    return bad;
}

/* do x[0..nx) and y[0..ny) agree as multisets? (sorts both) */
static int same_multiset(int *x, int nx, int *y, int ny) {
    if (nx != ny) return 0;
    qsort(x, (size_t)nx, sizeof(int), cmp_asc);
    qsort(y, (size_t)ny, sizeof(int), cmp_asc);
    return memcmp(x, y, (size_t)nx * sizeof(int)) == 0;
}

static int identities(void) {
    int bad = 0;
    for (int e = 0; e < 3; e++) {
        int m = EXC[e][0];
        const int *o = &EXC[e][1];
        int ok = balanced(o, 6, m) && !has_pair(o, 6, m) && generates(o, m)
                 && !move(o, m, 0) && !move(o, m, 1);
        printf("O%d balanced, without pair, generating, no move: %s\n", m, ok ? "yes" : "NO");
        bad |= !ok;
    }
    {
        int lhs[8] = {1, 4, 9, 15, 16, 18, 2, 19};
        int sig[4] = {2, 9, 16, 15}, q[4] = {1, 4, 18, 19};
        int rhs[8] = {2, 9, 16, 15, 1, 4, 18, 19};
        int ok = same_multiset(lhs, 8, rhs, 8) && balanced(sig, 4, 21) && balanced(q, 4, 21);
        printf("O21 + {2,19} = sigma(3,2) + Q, all parts balanced: %s\n", ok ? "yes" : "NO");
        bad |= !ok;
    }
    {
        const int ms[2] = {33, 39}, x1s[2] = {32, 32}, x2s[2] = {8, 5};
        const int pairs[2][4] = {{1, 65, 25, 41}, {5, 73, 7, 71}};
        const int qs[2][4] = {{1, 25, 44, 62}, {2, 7, 73, 74}};
        for (int r = 0; r < 2; r++) {
            int m = ms[r], M = 2 * m, x1 = x1s[r], x2 = x2s[r];
            int a[6], t1[4] = {x1, (x1 + m) % M, md(-2L * x1, M), m};
            int t2[4] = {x2, (x2 + m) % M, md(-2L * x2, M), m}, q[4];
            for (int i = 0; i < 6; i++) a[i] = 2 * EXC[r + 1][i + 1];
            for (int i = 0; i < 4; i++) q[i] = qs[r][i];
            int lhs[12], rhs[12];
            for (int i = 0; i < 6; i++) lhs[i] = a[i];
            for (int i = 0; i < 4; i++) lhs[6 + i] = pairs[r][i];
            lhs[10] = m; lhs[11] = m;
            for (int i = 0; i < 4; i++) { rhs[i] = q[i]; rhs[4 + i] = t1[i]; rhs[8 + i] = t2[i]; }
            int ok = balanced(a, 6, M) && balanced(q, 4, M) && balanced(t1, 4, M)
                     && balanced(t2, 4, M) && same_multiset(lhs, 12, rhs, 12);
            printf("2*O%d + pairs + {%d,%d} = Q + T(%d) + T(%d) at level %d, all parts balanced: %s\n",
                   m, m, m, x1, x2, M, ok ? "yes" : "NO");
            bad |= !ok;
        }
    }
    {
        int ok = 1;
        for (int M = 4; M <= 200; M += 2)
            for (int x = 1; x < M; x++) {
                if (2 * x % M == 0) continue;
                int t[4] = {x, (x + M / 2) % M, md(-2L * x, M), M / 2};
                if (!balanced(t, 4, M)) ok = 0;
            }
        printf("T(x) = {x, x+M/2, -2x, M/2} balanced for all even M <= 200: %s\n", ok ? "yes" : "NO");
        bad |= !ok;
    }
    return bad;
}

int main(int argc, char **argv) {
    int M = argc > 1 ? atoi(argv[1]) : 45;
    int bad = census(M);
    bad |= identities();
    if (bad) { printf("FAILURE\n"); return 1; }
    printf("every generating Hodge sextuple without a pair has a move or is exceptional\n");
    return 0;
}
