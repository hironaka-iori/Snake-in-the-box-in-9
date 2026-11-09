/* Simulated annealing for large induced linear forests with at most c paths in Q_n.
   Lower bounds only (witnesses are re-checked by check_witness.py).
   build: gcc -O2 -o forest_sa forest_sa.c -lm
   usage: ./forest_sa n c iters seed [T0 T1 W]  -> prints best |F| and the vertex list         */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

static int n, V, c;
static unsigned char in[1 << 10], best_in[1 << 10];
static int deg[1 << 10];
static int sz, edges;

static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void add(int u) { in[u] = 1; sz++; for (int i = 0; i < n; i++) { int w = u ^ (1 << i); deg[w]++; if (in[w]) edges++; } }
static void del(int u) { in[u] = 0; sz--; for (int i = 0; i < n; i++) { int w = u ^ (1 << i); deg[w]--; if (in[w]) edges--; } }

/* walk from endpoint a (deg<=1) along its path; return the other endpoint */
static int other_end(int a) {
    int prev = -1, cur = a;
    for (;;) {
        int nxt = -1;
        for (int i = 0; i < n; i++) { int w = cur ^ (1 << i); if (in[w] && w != prev) { nxt = w; break; } }
        if (nxt < 0) return cur;
        prev = cur; cur = nxt;
    }
}

static int stackv[64], ns;
static void kdel(int u) { del(u); stackv[ns++] = u; }

int main(int argc, char **argv) {
    n = atoi(argv[1]); c = atoi(argv[2]); long long iters = atoll(argv[3]); rs ^= (unsigned long long)atoll(argv[4]) * 2654435761ULL;
    double T0 = argc > 5 ? atof(argv[5]) : 1.0, T1 = argc > 6 ? atof(argv[6]) : 0.05, W = argc > 7 ? atof(argv[7]) : 1.5;
    V = 1 << n;
    int best = 0;
    double E = 0;
    for (long long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int u = rnd() % V;
        ns = 0;
        int oldsz = sz, oldP = sz - edges;
        if (in[u]) {
            kdel(u);
        } else {
            int nb[16], k = 0;
            for (int i = 0; i < n; i++) { int w = u ^ (1 << i); if (in[w]) nb[k++] = w; }
            while (k > 2) { int j = rnd() % k; kdel(nb[j]); nb[j] = nb[--k]; }
            for (int j = 0; j < k; j++) if (deg[nb[j]] >= 2) { /* nb[j] would get degree 3: drop one of its other neighbours or itself */
                int r = rnd() % 3;
                if (r == 0) { kdel(nb[j]); nb[j] = nb[--k]; j--; continue; }
                int cand[16], q = 0; for (int i = 0; i < n; i++) { int w = nb[j] ^ (1 << i); if (in[w]) cand[q++] = w; }
                kdel(cand[rnd() % q]);
            }
            /* recompute after deletions */
            k = 0; for (int i = 0; i < n; i++) { int w = u ^ (1 << i); if (in[w]) nb[k++] = w; }
            int ok = 1;
            for (int j = 0; j < k; j++) if (deg[nb[j]] >= 2) ok = 0;
            if (ok && k == 2 && other_end(nb[0]) == nb[1]) { kdel(nb[rnd() % 2]); }
            k = 0; for (int i = 0; i < n; i++) { int w = u ^ (1 << i); if (in[w]) nb[k++] = w; }
            for (int j = 0; j < k; j++) if (deg[nb[j]] >= 2) ok = 0;
            if (k > 2) ok = 0;
            if (ok && k == 2 && other_end(nb[0]) == nb[1]) ok = 0;
            if (!ok) { while (ns) add(stackv[--ns]); continue; }
            add(u); stackv[ns++] = -1 - u; /* mark addition */
        }
        int P = sz - edges;
        double En = -sz + W * (P > c ? P - c : 0);
        double Eo = -oldsz + W * (oldP > c ? oldP - c : 0);
        double dE = En - Eo;
        if (dE <= 0 || urand() < exp(-dE / T)) {
            E = En;
            if (P <= c && sz > best) { best = sz; memcpy(best_in, in, V); }
        } else {
            while (ns) { int x = stackv[--ns]; if (x < 0) del(-1 - x); else add(x); }
        }
    }
    printf("n=%d c=%d best=%d\n[", n, c, best);
    int first = 1;
    for (int u = 0; u < V; u++) if (best_in[u]) { printf(first ? "%d" : ",%d", u); first = 0; }
    printf("]\n");
    return 0;
}
