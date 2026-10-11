/* Finite checks for the Fermat varieties of degree 52: the characters alpha, alpha' and beta,
 * the order parity nu_13 on beta and on the generators of Aoki's group S_52, nu_13 on every
 * balanced multiset of 4 or 6 nonzero residues, and the exponent conditions of the block
 * families of degrees 14 and 5.  The output is line for line that of python/fermat52.py and
 * of julia/fermat52.jl. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define M 52
static const int ALPHA[5] = {1, 5, 16, 37, 45};
static const int ALPHA2[5] = {29, 18, 42, 50, 17};
static int nlines = 0;
static int U[M], nu = 0;

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int norm(const int *a, int n, int t) { int s = 0; for (int i = 0; i < n; i++) s += t * a[i] % M; return s / M; }
static int order(int y) { return M / gcd(y % M, M); }
static void fail(const char *w) { printf("FAIL %s\n", w); exit(1); }
static void line(const char *s) { printf("%s\n", s); nlines++; }

/* nondecreasing k-tuples a[0] <= ... <= a[k-1] in 1..M-1 */
static long cnt, odd;
static int cur[6];
static void rec(int pos, int lo, int k, int s) {
    if (pos == k) {
        if (s % M) return;
        for (int j = 0; j < nu; j++) {
            int w = 0;
            for (int i = 0; i < k; i++) w += U[j] * cur[i] % M;
            if (2 * w != k * M) return;
        }
        cnt++;
        int o = 0; for (int i = 0; i < k; i++) o += order(cur[i]) == 13;
        odd += o % 2;
        return;
    }
    for (int x = lo; x < M; x++) { cur[pos] = x; rec(pos + 1, x, k, s + x); }
}

static void family(const char *fname, const int *al, const char **names, const int E[5][5], const int *D, int deg) {
    char buf[256];
    int degs[5] = {0, 0, 0, 0, 0}, adeg = 0;
    for (int b = 0; b < 5; b++) {
        int w = 0, pos = 0, zero = 0;
        for (int k = 0; k < 5; k++) { w += al[k] * E[b][k]; degs[k] += E[b][k] * D[b]; pos |= E[b][k] > 0; zero |= E[b][k] == 0; }
        if (w % M || !pos || !zero) fail("family weight");
        adeg += w / M * D[b];
        snprintf(buf, sizeof buf, "family %s block %s (degree %d) exponents (%d, %d, %d, %d, %d) weight %d = %d*52",
                 fname, names[b], D[b], E[b][0], E[b][1], E[b][2], E[b][3], E[b][4], w, w / M); line(buf);
    }
    for (int k = 0; k < 5; k++) if (degs[k] != deg) fail("family degree");
    if (adeg != 2 * deg) fail("deg A");
}

int main(void) {
    char buf[512];
    int beta[10];
    for (int t = 1; t < M; t++) if (gcd(t, M) == 1) U[nu++] = t;
    for (int i = 0; i < 5; i++) { beta[i] = ALPHA[i]; beta[5 + i] = ALPHA2[i]; }
    int sa = 0, sb = 0, n2 = 0;
    for (int i = 0; i < 10; i++) if (beta[i] % M == 0) fail("zero entry");
    for (int i = 0; i < 5; i++) { sa += ALPHA[i]; sb += ALPHA2[i]; }
    if (sa % M || sb % M) fail("sum");
    for (int j = 0; j < nu; j++) {
        int x = norm(ALPHA, 5, U[j]), y = norm(ALPHA2, 5, U[j]);
        if (x < 2 || x > 3 || y < 2 || y > 3) fail("level one");
        if (x + y != 5) fail("complementary types");
        if (x == 2) n2++;
    }
    int a9[5];
    for (int i = 0; i < 5; i++) a9[i] = 9 * ALPHA2[i] % M;
    const int want9[5] = {1, 6, 14, 34, 49};
    if (memcmp(a9, want9, sizeof a9) || norm(a9, 5, 1) != 2 || norm(ALPHA, 5, 1) != 2) fail("|alpha| = |9 alpha'| = 2");
    snprintf(buf, sizeof buf, "alpha (%d, %d, %d, %d, %d) |alpha| = %d, |t alpha| in {2,3} for all %d units, %d of them 2",
             ALPHA[0], ALPHA[1], ALPHA[2], ALPHA[3], ALPHA[4], norm(ALPHA, 5, 1), nu, n2);
    line(buf);
    snprintf(buf, sizeof buf, "alpha' (%d, %d, %d, %d, %d), 9 alpha' = (%d, %d, %d, %d, %d) with |9 alpha'| = 2, |t alpha| + |t alpha'| = 5 for all %d units",
             ALPHA2[0], ALPHA2[1], ALPHA2[2], ALPHA2[3], ALPHA2[4], a9[0], a9[1], a9[2], a9[3], a9[4], nu);
    line(buf);
    strcpy(buf, "units t < 26:");
    for (int j = 0; j < nu && U[j] < 26; j++) {
        char w[32]; snprintf(w, sizeof w, " %d:%d%d", U[j], norm(ALPHA, 5, U[j]), norm(ALPHA2, 5, U[j])); strcat(buf, w);
    }
    line(buf);
    for (int i = 0; i < 10; i++) for (int j = i + 1; j < 10; j++) if ((beta[i] + beta[j]) % M == 0) fail("beta pair");
    for (int j = 0; j < nu; j++) if (norm(beta, 10, U[j]) != 5) fail("beta balanced");
    line("beta = alpha * alpha': |t beta| = 5 for all units t, no pair: Hodge character of X^8_52");

    int c13 = 0, last = -1;
    for (int i = 0; i < 10; i++) if (order(beta[i]) == 13) { c13++; last = beta[i]; }
    if (c13 != 1 || last != 16) fail("nu_13(beta)");
    snprintf(buf, sizeof buf, "nu_13(beta) = 1: the only entry of order 13 is %d", last); line(buf);
    int npairs = 0, nstd = 0;
    for (int y = 1; y < M; y++) { if (((order(y) == 13) + (order(M - y) == 13)) % 2) fail("pair parity"); npairs++; }
    const int primes[2] = {2, 13};
    for (int k = 0; k < 2; k++) {
        int p = primes[k], d = M / p;
        for (int i = 1; i < d; i++) {
            int c = 0;
            if (p == 2) { int e[4] = {i, i + d, (2 * M - 2 * i) % M, d}; for (int j = 0; j < 4; j++) c += order(e[j]) == 13; }
            else { for (int j = 0; j < p; j++) c += order(i + j * d) == 13; c += order(((-p * i) % M + M) % M) == 13; }
            if (c % 2) fail("standard parity");
            nstd++;
        }
    }
    snprintf(buf, sizeof buf, "nu_13 vanishes on S_52: %d pairs and %d standard characters checked", npairs, nstd); line(buf);

    for (int k = 4; k <= 6; k += 2) {
        cnt = 0; odd = 0; rec(0, 1, k, 0);
        if (odd) fail("small multiset with nu_13 = 1");
        snprintf(buf, sizeof buf, "balanced multisets of %d nonzero residues mod 52: %ld, all with nu_13 = 0", k, cnt); line(buf);
    }

    const char *na[5] = {"G", "s", "F", "t", "H"};
    const int EA[5][5] = {{0, 0, 0, 3, 1}, {0, 1, 1, 0, 3}, {2, 1, 0, 0, 1}, {0, 0, 13, 0, 0}, {0, 3, 0, 1, 0}};
    const int DA[5] = {4, 1, 7, 1, 2};
    family("A", ALPHA, na, EA, DA, 14);
    for (int b = 0; b < 5; b++) if (EA[b][0] && EA[b][2]) fail("chart (0,2)");
    line("family A: every u_k has degree 14, A has degree 28; (0,2) shares no block");
    const char *nb[5] = {"t", "s", "s-t", "L", "Q"};
    const int EB[5][5] = {{0, 0, 5, 1, 0}, {3, 0, 0, 0, 1}, {2, 0, 0, 3, 0}, {0, 3, 0, 1, 0}, {0, 1, 0, 0, 2}};
    const int DB[5] = {1, 1, 1, 1, 2};
    family("B", want9, nb, EB, DB, 5);
    for (int b = 0; b < 5; b++) if (EB[b][1] && EB[b][2]) fail("chart (1,2)");
    line("family B: every u_k has degree 5, A has degree 10; (1,2) shares no block");
    printf("%d lines, all checks passed\n", nlines);
    return 0;
}
