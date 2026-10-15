/* Block patterns of cor:patterns and the homomorphism nu_R of lem:nusqrt.
   Same checks and output as verification/python/patterns.py. */
#include <stdio.h>

typedef struct { int e[5]; int d; } col;
typedef struct { int m, D; int a[5]; int n; col c[5]; } row;

static const row ROWS[7] = {
    {114, 3, {51, 21, 86, 14, 56}, 4,
     {{{0, 0, 1, 2, 0}, 1}, {{0, 0, 2, 0, 1}, 1}, {{1, 3, 0, 0, 0}, 1}, {{2, 0, 0, 1, 2}, 1}}},
    {114, 24, {1, 25, 43, 57, 102}, 5,
     {{{3, 1, 2, 0, 0}, 7}, {{0, 1, 5, 0, 1}, 2}, {{0, 0, 0, 2, 0}, 12}, {{1, 5, 0, 0, 1}, 3},
      {{0, 0, 0, 0, 19}, 1}}},
    {44, 11, {1, 5, 8, 33, 41}, 5,
     {{{3, 0, 0, 0, 1}, 1}, {{0, 0, 11, 0, 0}, 1}, {{1, 1, 0, 0, 2}, 5}, {{1, 2, 0, 1, 0}, 3},
      {{0, 0, 0, 4, 0}, 2}}},
    {52, 14, {1, 5, 16, 37, 45}, 5,
     {{{0, 0, 0, 3, 1}, 4}, {{0, 1, 1, 0, 3}, 1}, {{2, 1, 0, 0, 1}, 7}, {{0, 0, 13, 0, 0}, 1},
      {{0, 3, 0, 1, 0}, 2}}},
    {52, 5, {1, 6, 14, 34, 49}, 5,
     {{{0, 0, 5, 1, 0}, 1}, {{3, 0, 0, 0, 1}, 1}, {{2, 0, 0, 3, 0}, 1}, {{0, 3, 0, 1, 0}, 1},
      {{0, 1, 0, 0, 2}, 2}}},
    {102, 6, {1, 34, 44, 56, 69}, 4,
     {{{0, 0, 0, 3, 2}, 1}, {{0, 0, 3, 0, 4}, 1}, {{0, 3, 0, 0, 0}, 2}, {{2, 0, 1, 1, 0}, 3}}},
    {102, 18, {5, 35, 51, 96, 17}, 5,
     {{{0, 0, 0, 0, 6}, 2}, {{0, 0, 0, 17, 0}, 1}, {{0, 0, 2, 0, 0}, 9}, {{0, 6, 0, 1, 0}, 1},
      {{3, 2, 0, 0, 1}, 6}}},
};

static int ok = 1;

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int nu(int M, const int *v, int n) {
    int c = 0;
    for (int i = 0; i < n; i++) if (v[i] * v[i] % M == 1) c++;
    return c % 2;
}

static void level(int M, int p1, int p2, const int O[6]) {
    int first = 1;
    printf("M=%d roots=", M);
    for (int y = 0; y < M; y++)
        if (y * y % M == 1) { printf(first ? "%d" : ",%d", y); first = 0; }
    for (int t = 1; t < M; t++) {
        if (gcd(t, M) != 1) continue;
        int s = 0;
        for (int k = 0; k < 6; k++) s += t * O[k] % M;
        if (s != 3 * M) { printf("\nFAIL O_%d is not balanced at t=%d\n", M, t); ok = 0; }
    }
    if (nu(M, O, 6) != 1) { printf("\nFAIL nu_R(O_%d) = 0\n", M); ok = 0; }
    for (int y = 1; y < M; y++) {
        int pr[2] = {y, M - y};
        if (nu(M, pr, 2) != 0) { printf("\nFAIL nu_R on the pair (%d,%d)\n", y, M - y); ok = 0; }
    }
    int nstd = 0, ps[2] = {p1, p2};
    for (int q = 0; q < 2; q++) {
        int p = ps[q], d = M / p;
        for (int i = 1; i < d; i++) {
            int s[16];
            for (int k = 0; k < p; k++) s[k] = i + k * d;
            s[p] = ((-p * i) % M + M) % M;
            nstd++;
            if (nu(M, s, p + 1) != 0) { printf("\nFAIL nu_R on sigma_{%d,%d}\n", p, i); ok = 0; }
        }
    }
    printf(" O=(");
    for (int k = 0; k < 6; k++) printf(k ? ",%d" : "%d", O[k]);
    printf(") in_O=");
    first = 1;
    for (int k = 0; k < 6; k++)
        if (O[k] * O[k] % M == 1) { printf(first ? "%d" : ",%d", O[k]); first = 0; }
    printf(" nu_R(O)=%d standard=%d pairs=%d\n", nu(M, O, 6), nstd, M - 1);
}

int main(void) {
    for (int r = 0; r < 7; r++) {
        const row *R = &ROWS[r];
        int m = R->m, D = R->D, s = 0, good = 1, degs = 0, w[5];
        for (int k = 0; k < 5; k++) { s += R->a[k]; if (R->a[k] <= 0 || R->a[k] >= m) good = 0; }
        if (!good || s != 2 * m) { printf("FAIL character at level %d\n", m); ok = 0; }
        for (int k = 0; k < 5; k++) {
            int cs = 0;
            for (int l = 0; l < R->n; l++) cs += R->c[l].e[k] * R->c[l].d;
            if (cs != D) { printf("FAIL (P1) at level %d, row %d\n", m, r); ok = 0; }
        }
        for (int l = 0; l < R->n; l++) {
            int pos = 0, zero = 0;
            w[l] = 0;
            for (int k = 0; k < 5; k++) {
                w[l] += R->a[k] * R->c[l].e[k];
                if (R->c[l].e[k] > 0) pos = 1;
                if (R->c[l].e[k] == 0) zero = 1;
            }
            if (!(R->c[l].d > 0 && pos && zero && w[l] % m == 0)) {
                printf("FAIL (P2) at level %d, row %d, column %d\n", m, r, l); ok = 0;
            }
            degs += R->c[l].d;
        }
        if (!(degs > D)) { printf("FAIL (P3) at level %d, row %d\n", m, r); ok = 0; }
        printf("m=%d alpha=(%d,%d,%d,%d,%d) D=%d degrees=%d weights=", m, R->a[0], R->a[1],
               R->a[2], R->a[3], R->a[4], D, degs);
        for (int l = 0; l < R->n; l++) printf(l ? ",%d" : "%d", w[l]);
        printf("\n");
    }
    static const int O33[6] = {1, 4, 16, 22, 25, 31}, O39[6] = {1, 7, 16, 22, 34, 37};
    level(33, 3, 11, O33);
    level(39, 3, 13, O39);
    if (!ok) return 1;
    printf("7 block patterns and nu_R at levels 33, 39: all checks passed\n");
    return 0;
}
