/* Finite checks for the Fermat varieties of degree 44: the characters alpha, b and beta,
 * the order parity nu_11 on beta and on the generators of Aoki's group S_44, nu_11 on every
 * balanced multiset of 4 or 6 nonzero residues, and the exponent conditions of the block
 * family of degree 11.  The output is line for line that of python/fermat44.py and of
 * julia/fermat44.jl. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define M 44
static const int ALPHA[5] = {1, 5, 8, 33, 41};
static const int B[3] = {9, 37, 42};
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
static void rec(int pos, int lo, int k) {
    if (pos == k) {
        int s = 0;
        for (int i = 0; i < k; i++) s += cur[i];
        if (s % M) return;
        for (int j = 0; j < nu; j++) {
            int w = 0;
            for (int i = 0; i < k; i++) w += U[j] * cur[i] % M;
            if (2 * w != k * M) return;
        }
        cnt++;
        int o = 0; for (int i = 0; i < k; i++) o += order(cur[i]) == 11;
        odd += o % 2;
        return;
    }
    for (int x = lo; x < M; x++) { cur[pos] = x; rec(pos + 1, x, k); }
}

int main(void) {
    char buf[512];
    int beta[8];
    for (int t = 1; t < M; t++) if (gcd(t, M) == 1) U[nu++] = t;
    for (int i = 0; i < 5; i++) beta[i] = ALPHA[i];
    for (int i = 0; i < 3; i++) beta[5 + i] = B[i];
    int sa = 0, sb = 0, n2 = 0;
    for (int i = 0; i < 8; i++) if (beta[i] % M == 0) fail("zero entry");
    for (int i = 0; i < 5; i++) sa += ALPHA[i];
    for (int i = 0; i < 3; i++) sb += B[i];
    if (sa % M || sb % M) fail("sum");
    for (int j = 0; j < nu; j++) {
        int x = norm(ALPHA, 5, U[j]), y = norm(B, 3, U[j]);
        if (x + y != 4) fail("complementary types");
        if (x == 2) n2++;
    }
    if (norm(ALPHA, 5, 1) != 2) fail("|alpha| = 2");
    snprintf(buf, sizeof buf, "alpha (%d, %d, %d, %d, %d) |alpha| = %d, |t alpha| in {2,3} for all %d units, %d of them 2",
             ALPHA[0], ALPHA[1], ALPHA[2], ALPHA[3], ALPHA[4], norm(ALPHA, 5, 1), nu, n2);
    line(buf);
    snprintf(buf, sizeof buf, "b (%d, %d, %d) |b| = %d, |t alpha| + |t b| = 4 for all %d units", B[0], B[1], B[2], norm(B, 3, 1), nu);
    line(buf);
    strcpy(buf, "units t < 22:");
    for (int j = 0; j < nu && U[j] < 22; j++) {
        char w[32]; snprintf(w, sizeof w, " %d:%d%d", U[j], norm(ALPHA, 5, U[j]), norm(B, 3, U[j])); strcat(buf, w);
    }
    line(buf);
    for (int i = 0; i < 8; i++) for (int j = i + 1; j < 8; j++) if ((beta[i] + beta[j]) % M == 0) fail("beta pair");
    for (int j = 0; j < nu; j++) if (norm(beta, 8, U[j]) != 4) fail("beta balanced");
    line("beta = alpha * b: |t beta| = 4 for all units t, no pair: Hodge character of X^6_44");

    int c11 = 0, last = -1;
    for (int i = 0; i < 8; i++) if (order(beta[i]) == 11) { c11++; last = beta[i]; }
    if (c11 != 1 || last != 8) fail("nu_11(beta)");
    snprintf(buf, sizeof buf, "nu_11(beta) = 1: the only entry of order 11 is %d", last); line(buf);
    int npairs = 0, nstd = 0;
    for (int y = 1; y < M; y++) { if (((order(y) == 11) + (order(M - y) == 11)) % 2) fail("pair parity"); npairs++; }
    const int primes[2] = {2, 11};
    for (int k = 0; k < 2; k++) {
        int p = primes[k], d = M / p;
        for (int i = 1; i < d; i++) {
            int c = 0;
            if (p == 2) { int e[4] = {i, i + d, (2 * M - 2 * i) % M, d}; for (int j = 0; j < 4; j++) c += order(e[j]) == 11; }
            else { for (int j = 0; j < p; j++) c += order(i + j * d) == 11; c += order(((-p * i) % M + M) % M) == 11; }
            if (c % 2) fail("standard parity");
            nstd++;
        }
    }
    snprintf(buf, sizeof buf, "nu_11 vanishes on S_44: %d pairs and %d standard characters checked", npairs, nstd); line(buf);

    for (int k = 4; k <= 6; k += 2) {
        cnt = 0; odd = 0; rec(0, 1, k);
        if (odd) fail("small multiset with nu_11 = 1");
        snprintf(buf, sizeof buf, "balanced multisets of %d nonzero residues mod 44: %ld, all with nu_11 = 0", k, cnt); line(buf);
    }

    const char *names[5] = {"s", "t", "P", "Q", "S"};
    const int E[5][5] = {{3, 0, 0, 0, 1}, {0, 0, 11, 0, 0}, {1, 1, 0, 0, 2}, {1, 2, 0, 1, 0}, {0, 0, 0, 4, 0}};
    const int D[5] = {1, 1, 5, 3, 2};
    int degs[5] = {0, 0, 0, 0, 0}, adeg = 0;
    for (int b = 0; b < 5; b++) {
        int w = 0, pos = 0, zero = 0;
        for (int k = 0; k < 5; k++) { w += ALPHA[k] * E[b][k]; degs[k] += E[b][k] * D[b]; pos |= E[b][k] > 0; zero |= E[b][k] == 0; }
        if (w % M || !pos || !zero) fail("family weight");
        adeg += w / M * D[b];
        snprintf(buf, sizeof buf, "family block %s (degree %d) exponents (%d, %d, %d, %d, %d) weight %d = %d*44",
                 names[b], D[b], E[b][0], E[b][1], E[b][2], E[b][3], E[b][4], w, w / M); line(buf);
    }
    for (int k = 0; k < 5; k++) if (degs[k] != 11) fail("family degree");
    if (adeg != 22) fail("deg A");
    line("family: every u_k has degree 11, A has degree 22; (0,2) shares no block");
    printf("%d lines, all checks passed\n", nlines);
    return 0;
}
