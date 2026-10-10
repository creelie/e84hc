/* Finite checks for the Fermat varieties of degree 114: the characters alpha1, alpha2 and
 * beta, the order parity nu_19 on beta and on the generators of Aoki's group S_114, and the
 * exponent conditions of the two block families of curves.  The output is line for line
 * that of python/fermat114.py --common and of julia/fermat114.jl --common. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define M 114
static const int A1[5] = {1, 25, 43, 57, 102};
static const int A2[5] = {39, 63, 68, 80, 92};
static int nlines = 0;

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int norm(const int *a, int n, int t) { int s = 0; for (int i = 0; i < n; i++) s += t * a[i] % M; return s / M; }
static int order(int y) { return M / gcd(y % M, M); }
static void fail(const char *w) { printf("FAIL %s\n", w); exit(1); }
static void line(const char *s) { printf("%s\n", s); nlines++; }

static void character(const char *name, const int *a) {
    char buf[256];
    int sum = 0, n2 = 0, nu = 0;
    for (int i = 0; i < 5; i++) { if (a[i] % M == 0) fail("zero entry"); sum += a[i]; }
    if (sum % M) fail("sum");
    for (int i = 0; i < 5; i++) for (int j = i + 1; j < 5; j++) if ((a[i] + a[j]) % M == 0) fail("pair");
    for (int t = 1; t < M; t++) {
        if (gcd(t, M) != 1) continue;
        int n = norm(a, 5, t);
        if (n != 2 && n != 3) fail("level");
        nu++; if (n == 2) n2++;
    }
    snprintf(buf, sizeof buf, "%s (%d, %d, %d, %d, %d) |a| = %d, |ta| in {2,3} for all %d units, %d of them 2",
             name, a[0], a[1], a[2], a[3], a[4], norm(a, 5, 1), nu, n2);
    line(buf);
}

int main(void) {
    char buf[256];
    int a2t[5], beta[10];
    for (int i = 0; i < 5; i++) { a2t[i] = 13 * A2[i] % M; beta[i] = A1[i]; beta[5 + i] = A2[i]; }
    character("alpha1", A1); character("alpha2", A2); character("13*alpha2", a2t);
    if (norm(A1, 5, 1) != 2 || norm(a2t, 5, 1) != 2) fail("|alpha| = 2");
    for (int t = 1; t < M; t++) if (gcd(t, M) == 1 && norm(A1, 5, t) + norm(A2, 5, t) != 5) fail("beta Hodge");
    for (int i = 0; i < 10; i++) for (int j = i + 1; j < 10; j++) if ((beta[i] + beta[j]) % M == 0) fail("beta pair");
    line("beta = alpha1 * alpha2: |t beta| = 5 for all units t, no pair: Hodge character of X^8_114");

    int cnt = 0, last = -1;
    for (int i = 0; i < 10; i++) if (order(beta[i]) == 19) { cnt++; last = beta[i]; }
    if (cnt != 1 || last != 102) fail("nu_19(beta)");
    snprintf(buf, sizeof buf, "nu_19(beta) = 1: the only entry of order 19 is %d", last); line(buf);
    int npairs = 0, nstd = 0;
    for (int y = 1; y < M; y++) { if (((order(y) == 19) + (order(M - y) == 19)) % 2) fail("pair parity"); npairs++; }
    const int primes[3] = {2, 3, 19};
    for (int k = 0; k < 3; k++) {
        int p = primes[k], d = M / p;
        for (int i = 1; i < d; i++) {
            int c = 0;
            if (p == 2) { int e[4] = {i, i + d, (2 * M - 2 * i) % M, d}; for (int j = 0; j < 4; j++) c += order(e[j]) == 19; }
            else { for (int j = 0; j < p; j++) c += order(i + j * d) == 19; c += order(((-p * i) % M + M) % M) == 19; }
            if (c % 2) fail("standard parity");
            nstd++;
        }
    }
    snprintf(buf, sizeof buf, "nu_19 vanishes on S_114: %d pairs and %d standard characters checked", npairs, nstd); line(buf);

    const char *n1[4] = {"0", "1", "lambda", "inf"};
    const int E1[4][5] = {{0, 0, 1, 2, 0}, {0, 0, 2, 0, 1}, {1, 3, 0, 0, 0}, {2, 0, 0, 1, 2}};
    for (int b = 0; b < 4; b++) {
        int w = 0; for (int k = 0; k < 5; k++) w += a2t[k] * E1[b][k];
        if (w % M) fail("family I weight");
        snprintf(buf, sizeof buf, "family I block %s exponents (%d, %d, %d, %d, %d) weight %d = %d*114",
                 n1[b], E1[b][0], E1[b][1], E1[b][2], E1[b][3], E1[b][4], w, w / M); line(buf);
    }
    for (int k = 0; k < 5; k++) { int d = 0; for (int b = 0; b < 4; b++) d += E1[b][k]; if (d != 3) fail("family I degree"); }
    line("family I: every u_k has degree 3, A has degree 6");
    const char *n2[5] = {"F", "H", "G", "K", "t"};
    const int E2[5][5] = {{3, 1, 2, 0, 0}, {0, 1, 5, 0, 1}, {0, 0, 0, 2, 0}, {1, 5, 0, 0, 1}, {0, 0, 0, 0, 19}};
    const int D2[5] = {7, 2, 12, 3, 1};
    int degs[5] = {0, 0, 0, 0, 0}, adeg = 0;
    for (int b = 0; b < 5; b++) {
        int w = 0; for (int k = 0; k < 5; k++) { w += A1[k] * E2[b][k]; degs[k] += E2[b][k] * D2[b]; }
        if (w % M) fail("family II weight");
        adeg += w / M * D2[b];
        snprintf(buf, sizeof buf, "family II block %s (degree %d) exponents (%d, %d, %d, %d, %d) weight %d = %d*114",
                 n2[b], D2[b], E2[b][0], E2[b][1], E2[b][2], E2[b][3], E2[b][4], w, w / M); line(buf);
    }
    for (int k = 0; k < 5; k++) if (degs[k] != 24) fail("family II degree");
    if (adeg != 48) fail("deg A");
    line("family II: every u_k has degree 24, A has degree 48");
    printf("%d lines, all checks passed\n", nlines);
    return 0;
}
