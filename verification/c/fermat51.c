/* Finite checks for the Fermat varieties of degree 51, at level 102: the characters alpha,
 * alpha' and beta, the order parity nu_17 on beta and on the generators of Aoki's group S_102,
 * nu_17 on every balanced multiset of 4 or 6 nonzero residues, and the exponent conditions of
 * the block families of degrees 6 and 18.  The output is line for line that of
 * python/fermat51.py and of julia/fermat51.jl. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define M 102
#define NU 32
static const int ALPHA[5] = {1, 7, 51, 60, 85};
static const int ALPHA2[5] = {91, 34, 26, 98, 57};
static int nlines = 0;
static int U[M], nu = 0;

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int norm(const int *a, int n, int t) { int s = 0; for (int i = 0; i < n; i++) s += t * a[i] % M; return s / M; }
static int order(int y) { return M / gcd(y % M, M); }
static void fail(const char *w) { printf("FAIL %s\n", w); exit(1); }
static void line(const char *s) { printf("%s\n", s); nlines++; }

/* nondecreasing h-tuples (h <= 3) of nonzero residues with their vectors f_t = sum <t a> */
typedef struct { int a[3]; int f[NU]; } half_t;
static int H;
static int cmpf(const void *x, const void *y) {
    return memcmp(((const half_t *)x)->f, ((const half_t *)y)->f, sizeof(int) * NU);
}
static long nhalves(int h, half_t **out) {
    long n = 0, cap = 1;
    for (int i = 0; i < h; i++) cap = cap * (M + i) / (i + 1);
    half_t *v = malloc(sizeof(half_t) * cap);
    int a[3];
    for (a[0] = 1; a[0] < M; a[0]++)
        for (a[1] = h > 1 ? a[0] : M - 1; a[1] < M; a[1]++)
            for (a[2] = h > 2 ? a[1] : M - 1; a[2] < M; a[2]++) {
                half_t *e = &v[n++];
                memcpy(e->a, a, sizeof a);
                for (int j = 0; j < nu; j++) { int s = 0; for (int i = 0; i < h; i++) s += U[j] * a[i] % M; e->f[j] = s; }
            }
    *out = v;
    return n;
}

static void family(const char *fname, const int *al, int nb, const char **names, const int E[][5], const int *D, int deg) {
    char buf[256];
    int degs[5] = {0, 0, 0, 0, 0}, adeg = 0;
    for (int b = 0; b < nb; b++) {
        int w = 0, pos = 0, zero = 0;
        for (int k = 0; k < 5; k++) { w += al[k] * E[b][k]; degs[k] += E[b][k] * D[b]; pos |= E[b][k] > 0; zero |= E[b][k] == 0; }
        if (w % M || !pos || !zero) fail("family weight");
        adeg += w / M * D[b];
        snprintf(buf, sizeof buf, "family %s block %s (degree %d) exponents (%d, %d, %d, %d, %d) weight %d = %d*102",
                 fname, names[b], D[b], E[b][0], E[b][1], E[b][2], E[b][3], E[b][4], w, w / M); line(buf);
    }
    for (int k = 0; k < 5; k++) if (degs[k] != deg) fail("family degree");
    if (adeg != 2 * deg) fail("deg A");
}

int main(void) {
    char buf[512];
    int beta[10];
    for (int t = 1; t < M; t++) if (gcd(t, M) == 1) U[nu++] = t;
    if (nu != NU) fail("number of units");
    for (int i = 0; i < 5; i++) { beta[i] = ALPHA[i]; beta[5 + i] = ALPHA2[i]; }
    int sa = 0, sb = 0, n2 = 0;
    for (int i = 0; i < 10; i++) if (beta[i] % M == 0) fail("zero entry");
    for (int i = 0; i < 5; i++) { sa += ALPHA[i]; sb += ALPHA2[i]; }
    if (sa != 2 * M || sb != 3 * M) fail("sum");
    for (int j = 0; j < nu; j++) {
        int x = norm(ALPHA, 5, U[j]), y = norm(ALPHA2, 5, U[j]);
        if (x < 2 || x > 3 || y < 2 || y > 3) fail("level one");
        if (x + y != 5) fail("complementary types");
        if (x == 2) n2++;
    }
    int a5[5], a37[5];
    for (int i = 0; i < 5; i++) { a5[i] = 5 * ALPHA[i] % M; a37[i] = 37 * ALPHA2[i] % M; }
    const int want5[5] = {5, 35, 51, 96, 17}, want37[5] = {1, 34, 44, 56, 69};
    if (memcmp(a5, want5, sizeof a5) || norm(a5, 5, 1) != 2) fail("|5 alpha| = 2");
    if (memcmp(a37, want37, sizeof a37) || norm(a37, 5, 1) != 2) fail("|37 alpha'| = 2");
    snprintf(buf, sizeof buf, "alpha (%d, %d, %d, %d, %d) |alpha| = %d, 5 alpha = (%d, %d, %d, %d, %d) with |5 alpha| = 2, |t alpha| in {2,3} for all %d units, %d of them 2",
             ALPHA[0], ALPHA[1], ALPHA[2], ALPHA[3], ALPHA[4], norm(ALPHA, 5, 1), a5[0], a5[1], a5[2], a5[3], a5[4], nu, n2);
    line(buf);
    snprintf(buf, sizeof buf, "alpha' (%d, %d, %d, %d, %d), 37 alpha' = (%d, %d, %d, %d, %d) with |37 alpha'| = 2, |t alpha| + |t alpha'| = 5 for all %d units",
             ALPHA2[0], ALPHA2[1], ALPHA2[2], ALPHA2[3], ALPHA2[4], a37[0], a37[1], a37[2], a37[3], a37[4], nu);
    line(buf);
    strcpy(buf, "units t < 51:");
    for (int j = 0; j < nu && U[j] < 51; j++) {
        char w[32]; snprintf(w, sizeof w, " %d:%d%d", U[j], norm(ALPHA, 5, U[j]), norm(ALPHA2, 5, U[j])); strcat(buf, w);
    }
    line(buf);
    for (int i = 0; i < 10; i++) for (int j = i + 1; j < 10; j++) if ((beta[i] + beta[j]) % M == 0) fail("beta pair");
    for (int j = 0; j < nu; j++) if (norm(beta, 10, U[j]) != 5) fail("beta balanced");
    line("beta = alpha * alpha': |t beta| = 5 for all units t, no pair: Hodge character of X^8_102");

    int c17 = 0, last = -1;
    for (int i = 0; i < 10; i++) if (order(beta[i]) == 17) { c17++; last = beta[i]; }
    if (c17 != 1 || last != 60) fail("nu_17(beta)");
    snprintf(buf, sizeof buf, "nu_17(beta) = 1: the only entry of order 17 is %d", last); line(buf);
    int npairs = 0, nstd = 0;
    for (int y = 1; y < M; y++) { if (((order(y) == 17) + (order(M - y) == 17)) % 2) fail("pair parity"); npairs++; }
    const int primes[3] = {2, 3, 17};
    for (int k = 0; k < 3; k++) {
        int p = primes[k], d = M / p;
        for (int i = 1; i < d; i++) {
            int c = 0;
            if (p == 2) { int e[4] = {i, i + d, (2 * M - 2 * i) % M, d}; for (int j = 0; j < 4; j++) c += order(e[j]) == 17; }
            else { for (int j = 0; j < p; j++) c += order(i + j * d) == 17; c += order(((-p * i) % M + M) % M) == 17; }
            if (c % 2) fail("standard parity");
            nstd++;
        }
    }
    snprintf(buf, sizeof buf, "nu_17 vanishes on S_102: %d pairs and %d standard characters checked", npairs, nstd); line(buf);

    /* A balanced multiset of k elements, sorted, splits into its k/2 smallest and k/2 largest
     * elements A and C with f(A) + f(C) = (k/2) M; the halves are matched through f. */
    for (int k = 4; k <= 6; k += 2) {
        half_t *v, key;
        H = k / 2;
        long n = nhalves(H, &v), cnt = 0, odd = 0;
        qsort(v, n, sizeof(half_t), cmpf);
        for (long x = 0; x < n; x++) {
            for (int j = 0; j < nu; j++) key.f[j] = H * M - v[x].f[j];
            half_t *hit = bsearch(&key, v, n, sizeof(half_t), cmpf);
            if (!hit) continue;
            long lo = hit - v, hi = lo;
            while (lo > 0 && !cmpf(&v[lo - 1], &key)) lo--;
            while (hi + 1 < n && !cmpf(&v[hi + 1], &key)) hi++;
            for (long y = lo; y <= hi; y++) {
                if (v[y].a[0] < v[x].a[H - 1]) continue;
                cnt++;
                int o = 0;
                for (int i = 0; i < H; i++) o += (order(v[x].a[i]) == 17) + (order(v[y].a[i]) == 17);
                odd += o % 2;
            }
        }
        free(v);
        if (odd) fail("small multiset with nu_17 = 1");
        snprintf(buf, sizeof buf, "balanced multisets of %d nonzero residues mod 102: %ld, all with nu_17 = 0", k, cnt); line(buf);
    }

    const char *na[4] = {"s", "t", "Q", "F"};
    const int EA[4][5] = {{0, 0, 0, 3, 2}, {0, 0, 3, 0, 4}, {0, 3, 0, 0, 0}, {2, 0, 1, 1, 0}};
    const int DA[4] = {1, 1, 2, 3};
    family("A", want37, 4, na, EA, DA, 6);
    for (int b = 0; b < 4; b++) if (EA[b][0] && EA[b][4]) fail("chart (0,4)");
    line("family A: every u_k has degree 6, A has degree 12; (0,4) shares no block");
    const char *nb[5] = {"Q", "t", "F", "s", "G"};
    const int EB[5][5] = {{0, 0, 0, 0, 6}, {0, 0, 0, 17, 0}, {0, 0, 2, 0, 0}, {0, 6, 0, 1, 0}, {3, 2, 0, 0, 1}};
    const int DB[5] = {2, 1, 9, 1, 6};
    family("B", want5, 5, nb, EB, DB, 18);
    for (int b = 0; b < 5; b++) if (EB[b][2] && EB[b][3]) fail("chart (2,3)");
    line("family B: every u_k has degree 18, A has degree 36; (2,3) shares no block");
    printf("%d lines, all checks passed\n", nlines);
    return 0;
}
