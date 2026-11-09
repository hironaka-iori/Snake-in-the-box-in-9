/* Simulated annealing for "locally forest-like" sets in Q_n: induced subgraphs of maximum
   degree <= 2 with at most c path components, in which every cycle component spans more than
   k coordinate directions (so no cycle lies inside a k-subcube).  Any such set satisfies every
   constraint of a k-subcube-local density LP for induced linear forests with c paths, so its
   size is a LOWER bound on the LP optimum (an obstruction to the method).
   build: gcc -O2 -o fake_sa fake_sa.c -lm
   usage: ./fake_sa n c k iters seed [T0 T1 W]  -> best size, then the vertex list          */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

static int n, V, c, K;
static unsigned char in[1 << 10], best_in[1 << 10];
static int deg[1 << 10];
static int sz, edges;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static void add(int u) { in[u] = 1; sz++; for (int i = 0; i < n; i++) { int w = u ^ (1 << i); deg[w]++; if (in[w]) edges++; } }
static void del(int u) { in[u] = 0; sz--; for (int i = 0; i < n; i++) { int w = u ^ (1 << i); deg[w]--; if (in[w]) edges--; } }

/* walk the path from endpoint a; return other endpoint, OR the direction mask used */
static int walk(int a, int *mask) {
    int prev = -1, cur = a; *mask = 0;
    for (;;) {
        int nxt = -1;
        for (int i = 0; i < n; i++) { int w = cur ^ (1 << i); if (in[w] && w != prev) { nxt = w; *mask |= 1 << i; break; } }
        if (nxt < 0) return cur;
        prev = cur; cur = nxt;
    }
}
static int stackv[64], ns;
static void kdel(int u) { del(u); stackv[ns++] = u; }

int main(int argc, char **argv) {
    n = atoi(argv[1]); c = atoi(argv[2]); K = atoi(argv[3]); long long iters = atoll(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 2654435761ULL;
    double T0 = argc > 6 ? atof(argv[6]) : 1.0, T1 = argc > 7 ? atof(argv[7]) : 0.05, W = argc > 8 ? atof(argv[8]) : 1.5;
    V = 1 << n;
    int best = 0;
    for (long long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int u = rnd() % V;
        ns = 0;
        int oldsz = sz, oldP = sz - edges;
        if (in[u]) kdel(u);
        else {
            int nb[16], k = 0;
            for (int i = 0; i < n; i++) { int w = u ^ (1 << i); if (in[w]) nb[k++] = w; }
            while (k > 2) { int j = rnd() % k; kdel(nb[j]); nb[j] = nb[--k]; }
            for (int j = 0; j < k; j++) if (deg[nb[j]] >= 2) {
                int r = rnd() % 3;
                if (r == 0) { kdel(nb[j]); nb[j] = nb[--k]; j--; continue; }
                int cand[16], q = 0; for (int i = 0; i < n; i++) { int w = nb[j] ^ (1 << i); if (in[w]) cand[q++] = w; }
                kdel(cand[rnd() % q]);
            }
            k = 0; for (int i = 0; i < n; i++) { int w = u ^ (1 << i); if (in[w]) nb[k++] = w; }
            int ok = (k <= 2);
            for (int j = 0; j < k; j++) if (deg[nb[j]] >= 2) ok = 0;
            if (ok && k == 2) {
                int m; if (walk(nb[0], &m) == nb[1]) {   /* closes a cycle */
                    m |= (u ^ nb[0]) | (u ^ nb[1]);
                    if (__builtin_popcount(m) <= K) ok = 0;
                }
            }
            if (!ok) { while (ns) add(stackv[--ns]); continue; }
            add(u); stackv[ns++] = -1 - u;
        }
        int P = sz - edges;   /* number of path components (cycles have v = e) */
        double En = -sz + W * (P > c ? P - c : 0), Eo = -oldsz + W * (oldP > c ? oldP - c : 0);
        double dE = En - Eo;
        if (dE <= 0 || urand() < exp(-dE / T)) {
            if (P <= c && sz > best) { best = sz; memcpy(best_in, in, V); }
        } else {
            while (ns) { int x = stackv[--ns]; if (x < 0) del(-1 - x); else add(x); }
        }
    }
    printf("n=%d c=%d k=%d best=%d\n[", n, c, K, best);
    int first = 1;
    for (int u = 0; u < V; u++) if (best_in[u]) { printf(first ? "%d" : ",%d", u); first = 0; }
    printf("]\n");
    return 0;
}
