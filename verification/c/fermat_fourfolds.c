/* Hodge characters of Fermat surfaces and fourfolds of degree prime to 6.
 *
 * For every m prime to 6 with 5 <= m <= M (M from the command line, default 55)
 * this program lists, by exhaustive search, the multisets of four and of six
 * nonzero residues mod m with sum zero whose representatives in [0, m) add up
 * to 2m (four entries) or 3m (six entries) after multiplication by every unit
 * t.  These are the Hodge characters of the Fermat surface and fourfold of
 * degree m (Proposition 3.6 of the paper).  It checks the classification of
 * Theorem 3.9: every such quadruple contains a pair a, -a, and every such
 * sextuple contains a pair or is 5-standard, {x, x+m/5, ..., x+4m/5, -5x}.
 *
 * Output, one line per m:
 *   H <m> quadruples <q> without_pair 0 sextuples <s> without_pair <n> 5-standard <n>
 * The program exits with status 1 if a counterexample appears.
 */
#include <stdio.h>
#include <stdlib.h>

static int m, nu, units[4096];

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int balanced(const int *a, int n, int h) {
    for (int j = 0; j < nu; j++) {
        long s = 0;
        for (int i = 0; i < n; i++) s += (long)units[j] * a[i] % m;
        if (s != h) return 0;
    }
    return 1;
}

static int has_pair(const int *a, int n) {
    for (int i = 0; i < n; i++)
        for (int k = i + 1; k < n; k++)
            if ((a[i] + a[k]) % m == 0) return 1;
    return 0;
}

/* a[0..5] sorted; is it {x + j m/5 : j < 5} together with -5x? */
static int standard5(const int *a) {
    if (m % 5) return 0;
    for (int i = 0; i < 6; i++) {
        int r[5], k = 0;
        for (int j = 0; j < 6; j++) if (j != i) r[k++] = a[j];
        int ok = 1;
        for (int j = 0; j < 5 && ok; j++) {
            if ((5L * r[j] - 5L * r[0]) % m) ok = 0;          /* same image under 5 */
            for (int l = j + 1; l < 5; l++) if (r[j] == r[l]) ok = 0; /* distinct */
        }
        if (ok && (a[i] + 5L * r[0]) % m == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    int M = argc > 1 ? atoi(argv[1]) : 55, bad = 0;
    for (m = 5; m <= M; m++) {
        if (m % 2 == 0 || m % 3 == 0) continue;
        nu = 0;
        for (int t = 1; t < m; t++) if (gcd(t, m) == 1) units[nu++] = t;
        long q = 0, qn = 0, s = 0, sn = 0, ss = 0;
        int a[6];
        for (a[0] = 1; a[0] < m; a[0]++)
        for (a[1] = a[0]; a[1] < m; a[1]++)
        for (a[2] = a[1]; a[2] < m; a[2]++) {
            a[3] = (int)((3L * m - a[0] - a[1] - a[2]) % m);
            if (a[3] >= a[2] && a[0] + a[1] + a[2] + a[3] == 2 * m && balanced(a, 4, 2 * m)) {
                q++;
                if (!has_pair(a, 4)) { qn++; bad = 1; }
            }
            for (a[3] = a[2]; a[3] < m; a[3]++)
            for (a[4] = a[3]; a[4] < m; a[4]++) {
                long t5 = (long)a[0] + a[1] + a[2] + a[3] + a[4];
                a[5] = (int)((5L * m - t5) % m);
                if (a[5] < a[4] || t5 + a[5] != 3L * m || !balanced(a, 6, 3 * m)) continue;
                s++;
                if (!has_pair(a, 6)) {
                    sn++;
                    if (standard5(a)) ss++; else bad = 1;
                }
            }
        }
        printf("H %d quadruples %ld without_pair %ld sextuples %ld without_pair %ld 5-standard %ld\n",
               m, q, qn, s, sn, ss);
    }
    if (bad) { printf("COUNTEREXAMPLE FOUND\n"); return 1; }
    printf("all Hodge quadruples have a pair; all Hodge sextuples have a pair or are 5-standard\n");
    return 0;
}
