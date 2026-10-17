/* Knuth random-probe estimator (and exact counter) for the snake DFS tree used by
 * work/snake_dfs.c (same node definition, same parity + leaf-peeling bound).
 *
 *   knuth est   N T PROBES SEED SYM [KEEP]   (KEEP>0: read one prefix "k v0 .. v_{k-1}" from stdin)
 *   knuth exact N T NODELIMIT SYM [KEEP]
 *
 * SYM=1: start at vertex 0, coordinates introduced in increasing order (Davies 1965),
 *        i.e. the first use of coordinate k requires coordinates 0..k-1 already used.
 * Node = one call of the DFS (also counted when the bound prunes it), as in snake_dfs.c.
 * Output: estimated (or exact) total nodes, and per-depth node profile.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXV 512
#define W64 8
typedef struct { uint64_t w[W64]; } bs;
static int N, NV;
static bs NB[MAXV], CN[MAXV], PAR[2];
static int use_peel = 1;

static inline void bs_clear(bs *a) { memset(a, 0, sizeof *a); }
static inline void bs_set(bs *a, int v) { a->w[v >> 6] |= 1ULL << (v & 63); }
static inline int bs_has(const bs *a, int v) { return (a->w[v >> 6] >> (v & 63)) & 1; }
static inline void bs_or(bs *a, const bs *b) { for (int i = 0; i < W64; i++) a->w[i] |= b->w[i]; }
static inline int bs_count_and(const bs *a, const bs *b) {
    int c = 0; for (int i = 0; i < W64; i++) c += __builtin_popcountll(a->w[i] & b->w[i]); return c;
}
static void init_cube(int n) {
    N = n; NV = 1 << n; bs_clear(&PAR[0]); bs_clear(&PAR[1]);
    for (int v = 0; v < NV; v++) {
        bs_clear(&NB[v]);
        for (int k = 0; k < n; k++) bs_set(&NB[v], v ^ (1 << k));
        CN[v] = NB[v]; bs_set(&CN[v], v); bs_set(&PAR[__builtin_popcount(v) & 1], v);
    }
}
/* identical to snake_dfs.c region_bound with allowed = all */
static int region_bound(int head, const bs *ban) {
    static int queue[MAXV];
    bs seen; bs_clear(&seen);
    int qh = 0, qt = 0;
    for (int k = 0; k < N; k++) { int u = head ^ (1 << k);
        if (bs_has(ban, u) || bs_has(&seen, u)) continue; bs_set(&seen, u); queue[qt++] = u; }
    while (qh < qt) { int u = queue[qh++];
        for (int k = 0; k < N; k++) { int x = u ^ (1 << k);
            if (bs_has(&seen, x) || bs_has(ban, x)) continue; bs_set(&seen, x); queue[qt++] = x; } }
    int p = __builtin_popcount(head) & 1;
    int opp = bs_count_and(&seen, &PAR[p ^ 1]), same = bs_count_and(&seen, &PAR[p]);
    int a = opp < same + 1 ? opp : same + 1, b = same < opp ? same : opp;
    int parity_bound = a + b;
    if (!use_peel || qt == 0) return parity_bound;
    static int deg[MAXV], round_of[MAXV], peel[MAXV];
    bs region = seen; bs_set(&region, head);
    int ph = 0, pt = 0;
    for (int i = 0; i < qt; i++) { int u = queue[i], d = 0;
        for (int k = 0; k < N; k++) d += bs_has(&region, u ^ (1 << k));
        deg[u] = d; round_of[u] = 0; if (d <= 1) { round_of[u] = 1; peel[pt++] = u; } }
    int removed = 0, maxround = 0;
    while (ph < pt) { int u = peel[ph++]; removed++;
        if (round_of[u] > maxround) maxround = round_of[u];
        for (int k = 0; k < N; k++) { int x = u ^ (1 << k);
            if (x == head || !bs_has(&seen, x) || round_of[x]) continue;
            if (--deg[x] <= 1) { round_of[x] = round_of[u] + 1; peel[pt++] = x; } } }
    int peel_bound = (qt - removed) + maxround;
    return peel_bound < parity_bound ? peel_bound : parity_bound;
}

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int T, SYM;
static int path[MAXV], plen;

/* children of current node (after bound passes); returns count, fills ch[] */
static int children(const bs *ban, int maxused, int *ch) {
    int head = path[plen - 1], c = 0;
    int lim = SYM ? (maxused + 1 < N - 1 ? maxused + 1 : N - 1) : N - 1;
    for (int k = 0; k <= lim; k++) { int x = head ^ (1 << k); if (!bs_has(ban, x)) ch[c++] = k; }
    return c;
}
/* does node pass (i.e. have children explored)? */
static int expandable(const bs *ban) {
    if (plen >= T) return 0;
    int ub = region_bound(path[plen - 1], ban);
    return plen + ub >= T;
}

static double prof_sum[MAXV + 2], prof_sq[MAXV + 2];
static long long exact_prof[MAXV + 2];
static long long nodes, node_limit; static int aborted, reachedT;

static void dfs_exact(bs ban, int maxused) {
    if (aborted) return;
    if (++nodes > node_limit) { aborted = 1; return; }
    exact_prof[plen]++;
    if (plen >= T) { reachedT++; return; }
    if (!expandable(&ban)) return;
    int ch[16]; int c = children(&ban, maxused, ch);
    int head = path[plen - 1];
    bs nb = ban; bs_or(&nb, &CN[head]);
    for (int i = 0; i < c; i++) { int k = ch[i];
        path[plen++] = head ^ (1 << k);
        dfs_exact(nb, k > maxused ? k : maxused);
        plen--; if (aborted) return; }
}


/* Sequential Monte Carlo (resample every step) estimate of Z_d = #(canonical directed
   induced paths with d vertices whose every prefix passes the bound for target T). */
typedef struct { bs ban; int maxused; int len; int head; } walk_t;
static void smc(int K, double beta, int every) {
    walk_t *A = malloc(sizeof(walk_t) * K), *B = malloc(sizeof(walk_t) * K);
    double *w = malloc(sizeof(double) * K), *cw = malloc(sizeof(double) * K);
    for (int i = 0; i < K; i++) { bs_clear(&A[i].ban); bs_set(&A[i].ban, 0); A[i].maxused = -1; A[i].len = 1; A[i].head = 0; }
    double logZ = 0; /* log10 */
    printf("{\"mode\":\"smc\",\"n\":%d,\"T\":%d,\"K\":%d,\"beta\":%.3f,\"log10Z\":[0", N, T, K, beta);
    for (int d = 1; d < T; d++) {
        double tot = 0; int alive = 0;
        for (int i = 0; i < K; i++) {
            walk_t *a = &A[i]; int head = a->head;
            bs nb = a->ban; bs_or(&nb, &CN[head]);
            int lim = SYM ? (a->maxused + 1 < N - 1 ? a->maxused + 1 : N - 1) : N - 1;
            double wt[16], s = 0; int ks[16], c = 0;
            for (int k = 0; k <= lim; k++) { int x = head ^ (1 << k); if (bs_has(&a->ban, x)) continue;
                int ub = (d + 1 >= T) ? 0 : region_bound(x, &nb);
                if (d + 1 + ub >= T) { ks[c] = k; wt[c] = exp(beta * ub); s += wt[c]; c++; } }
            if (!c) { w[i] = 0; continue; }
            double r = (double)(rnd() >> 11) / 9007199254740992.0 * s; int pick = c - 1;
            for (int j = 0; j < c; j++) { if (r < wt[j]) { pick = j; break; } r -= wt[j]; }
            w[i] = s / wt[pick];
            int k = ks[pick]; a->ban = nb; a->head = head ^ (1 << k); a->len++; if (k > a->maxused) a->maxused = k;
            tot += w[i]; alive++;
        }
        if (tot <= 0) { printf(",null"); for (int e = d + 2; e <= T; e++) printf(",null"); break; }
        logZ += log10(tot / K);
        printf(",%.4f", logZ);
        /* systematic resampling */
        double acc = 0; for (int i = 0; i < K; i++) { acc += w[i]; cw[i] = acc; }
        double u = (double)(rnd() >> 11) / 9007199254740992.0 * (acc / K); int j = 0;
        for (int i = 0; i < K; i++) { double t = u + i * (acc / K); while (j < K - 1 && cw[j] <= t) j++; B[i] = A[j]; }
        walk_t *tmp = A; A = B; B = tmp;
        if (every && d % every == 0) { int distinct = 0; for (int i = 0; i < K; i++) if (i == 0 || A[i].head != A[i-1].head || memcmp(&A[i].ban, &A[i-1].ban, sizeof(bs))) distinct++;
            fprintf(stderr, "d=%d alive=%d distinct~%d log10Z=%.3f\n", d + 1, alive, distinct, logZ); }
    }
    printf("]}\n");
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    const char *mode = argv[1]; init_cube(atoi(argv[2])); T = atoi(argv[3]);
    if (getenv("NO_PEEL")) use_peel = 0;
    if (!strcmp(mode, "smc")) {
        int K = atoi(argv[4]); uint64_t sd = atoll(argv[5]); SYM = atoi(argv[6]); double beta = atof(argv[7]);
        int every = argc > 8 ? atoi(argv[8]) : 0;
        rs ^= sd * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        smc(K, beta, every); return 0;
    }

    long long P = atoll(argv[4]); SYM = atoi(argv[argc > 6 && strcmp(mode, "est") == 0 ? 6 : 5]);
    int keep = 0; uint64_t seed = 1;
    if (!strcmp(mode, "est")) { seed = atoll(argv[5]); SYM = atoi(argv[6]); keep = argc > 7 ? atoi(argv[7]) : 0; }
    else { node_limit = P; SYM = atoi(argv[5]); keep = argc > 6 ? atoi(argv[6]) : 0; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    bs ban0; bs_clear(&ban0); int maxused0 = -1;
    if (keep > 0) {
        int k; if (scanf("%d", &k) != 1) return 2; int s[MAXV];
        for (int i = 0; i < k; i++) if (scanf("%d", &s[i]) != 1) return 2;
        for (int i = 0; i < keep; i++) { path[i] = s[i]; if (i < keep - 1) bs_or(&ban0, &CN[s[i]]); }
        bs_set(&ban0, s[keep - 1]); plen = keep; SYM = 0;
    } else { path[0] = 0; plen = 1; bs_set(&ban0, 0); }
    int base = plen;
    if (!strcmp(mode, "exact")) {
        nodes = 0; dfs_exact(ban0, maxused0);
        printf("{\"mode\":\"exact\",\"n\":%d,\"T\":%d,\"sym\":%d,\"keep\":%d,\"nodes\":%lld,\"aborted\":%d,\"reachedT\":%d,\"profile\":[", N, T, SYM, keep, nodes, aborted, reachedT);
        for (int d = base; d <= T; d++) printf("%s%lld", d > base ? "," : "", exact_prof[d]);
        printf("]}\n"); return 0;
    }
    /* Knuth estimator */
    double sum = 0, sumsq = 0, maxX = 0; long long probes_deep = 0; int maxdepth = 0;
    double *Xs = malloc(sizeof(double) * P);
    for (long long p = 0; p < P; p++) {
        plen = base; bs ban = ban0; int maxused = maxused0;
        double prod = 1, X = 1; static double prof_p[MAXV + 2];
        for (int d = 0; d <= T + 1; d++) prof_p[d] = 0;
        prof_p[plen] = 1;
        while (1) {
            if (!expandable(&ban)) break;
            int ch[16]; int c = children(&ban, maxused, ch);
            if (c == 0) break;
            prod *= c; int k = ch[rnd() % c];
            int head = path[plen - 1]; bs_or(&ban, &CN[head]);
            path[plen++] = head ^ (1 << k); if (k > maxused) maxused = k;
            X += prod; prof_p[plen] += prod;
        }
        if (plen > maxdepth) maxdepth = plen;
        Xs[p] = X; sum += X; sumsq += X * X; if (X > maxX) maxX = X;
        for (int d = base; d <= T; d++) { prof_sum[d] += prof_p[d]; prof_sq[d] += prof_p[d] * prof_p[d]; }
    }
    double mean = sum / P, var = sumsq / P - mean * mean; if (var < 0) var = 0;
    double se = sqrt(var / P);
    /* median of log10 X */
    double lsum = 0; for (long long p = 0; p < P; p++) lsum += log10(Xs[p]);
    printf("{\"mode\":\"est\",\"n\":%d,\"T\":%d,\"sym\":%d,\"keep\":%d,\"probes\":%lld,\"seed\":%llu,"
           "\"mean\":%.6e,\"se\":%.6e,\"maxX\":%.6e,\"max_share\":%.4f,\"mean_log10X\":%.3f,\"maxdepth\":%d,\"profile\":[",
           N, T, SYM, keep, P, (unsigned long long)seed, mean, se, maxX, maxX / sum, lsum / P, maxdepth);
    for (int d = base; d <= T; d++) printf("%s%.4e", d > base ? "," : "", prof_sum[d] / P);
    printf("],\"profile_se\":[");
    for (int d = base; d <= T; d++) { double m = prof_sum[d] / P, v = prof_sq[d] / P - m * m; if (v < 0) v = 0;
        printf("%s%.3e", d > base ? "," : "", sqrt(v / P)); }
    printf("]}\n");
    return 0;
}
