/* Helpers for refine_fast --lean --incremental / --tight-cycles (see fastround.py).
   Graph in CSR form by source (LeanAutomaton.edges): edges starts[u] .. starts[u+1]-1 go to V[e].
   Build: cc -O2 -shared -fPIC -o fastround_c.so fastround_c.c */
#include <stdint.h>
/* Weight type: uint8_t (alpha), or uint16_t with -DWEIGHT16 (den * alpha + share lower bound; the
   same source is built twice, fastround_c.so / fastround_c16.so, leanmin_c.so / leanmin_c16.so). */
#ifdef WEIGHT16
typedef uint16_t wt_t;
#else
typedef uint8_t wt_t;
#endif
#include <stdlib.h>
#include <string.h>
#include <math.h>

/* prune_masked: m[e] (edge mask, in/out) := edges of the largest subgraph of {e : m[e]} in which every
   state has an out-edge and an in-edge (same fixpoint as refine_fast.prune on the masked edge set).
   Returns the number of passes. */
int prune_masked(int64_t n, const int64_t *starts, const int32_t *V, uint8_t *m)
{
    uint8_t *alive = malloc(n), *out = malloc(n), *inn = malloc(n);
    memset(alive, 1, n);
    int passes = 0;
    for (;;) {
        passes++;
        memset(out, 0, n); memset(inn, 0, n);
        for (int64_t u = 0; u < n; u++) {
            int64_t a = starts[u], b = starts[u + 1];
            if (!alive[u]) { memset(m + a, 0, b - a); continue; }
            for (int64_t e = a; e < b; e++) {
                if (!m[e]) continue;
                int32_t v = V[e];
                if (!alive[v]) { m[e] = 0; continue; }
                out[u] = 1; inn[v] = 1;
            }
        }
        int changed = 0;
        for (int64_t u = 0; u < n; u++)
            if (alive[u] && !(out[u] && inn[u])) { alive[u] = 0; changed = 1; }
        if (!changed) break;
    }
    free(alive); free(out); free(inn);
    return passes;
}

/* tight_cycles: after a converged Howard solve (eta = per-state optimal mean, val = bias with
   val[u] = W[pol u] - eta[u] + val[V[pol u]]), every alive edge u->v with eta[u] == eta[v] has reduced
   cost rc = W - eta[u] + val[v] - val[u] >= 0 (Howard stops when no edge improves val), eta never
   decreases along an edge, so every cycle lies in one eta class and has mean eta + (sum rc) / length.
   Depth-first walks through the edges with eta[u] == eta[v] <= cap and rc <= level, smallest rc first
   (policy edges have rc 0; on ties an edge that closes a cycle), closing a cycle whenever the walk meets
   its own path.  A cycle is kept when its rc sum <= f (cap - eta) * length (f: level below) and length <=
   max_len; otherwise its closing edge is skipped for the rest of the level.  Kept cycles are
   edge-disjoint (their edges are switched off in `alive` during the search; everything is restored
   before returning).  Levels with f = 0, 1/2^(nlev-2), ..., 1/2, 1 (cheap cycles first): edges with
   rc <= f eps, cycles with mean <= eta + f (cap - eta).  In each level the
   start states are those with eta <= mu0 + 1e-9 first, then the rest with eta <= cap, in index order.
   Walks deeper than max_depth give up (the state is marked exhausted for that level).
   Output: cycle c has edges out_edges[out_off[c] .. out_off[c+1]-1] (in walk order).
   Returns the number of cycles. */
int64_t tight_cycles(int64_t n, const int64_t *starts, const int32_t *V, const wt_t *W, uint8_t *alive,
                     const double *eta, const double *val, double mu0, double cap, double eps, int nlev,
                     int64_t max_cycles, int64_t max_len, int64_t max_depth, int64_t max_out,
                     int64_t *out_edges, int64_t *out_off)
{
    uint8_t *dead = malloc(n), *onpath = calloc(n, 1);
    int64_t *path = malloc(sizeof(int64_t) * (max_depth + 1)), *pedge = malloc(sizeof(int64_t) * (max_depth + 1));
    double *cum = malloc(sizeof(double) * (max_depth + 1));       /* rc sum along the path */
    int64_t dcap = 1 << 16, nd = 0, *dropped = malloc(sizeof(int64_t) * dcap);
    int64_t nc = 0, no = 0; int full = 0;
    out_off[0] = 0;
    for (int lev = 0; lev < nlev && nc < max_cycles && !full; lev++) {
        double frac = lev == 0 ? 0.0 : 1.0 / (double)(1 << (nlev - 1 - lev));
        double level = frac * eps;
        memset(dead, 0, n);
        for (int tier = 0; tier < 2 && nc < max_cycles && !full; tier++) {
            double lim = tier == 0 ? mu0 + 1e-9 : cap;
            for (int64_t s = 0; s < n && nc < max_cycles && !full; s++) {
                if (dead[s] || !(eta[s] <= lim)) continue;
                if (tier == 1 && eta[s] <= mu0 + 1e-9) continue;
                int64_t len = 1; path[0] = s; onpath[s] = 1; cum[0] = 0.0;
                while (len > 0 && nc < max_cycles && !full) {
                    int64_t x = path[len - 1];
                    double ex = eta[x], lim_rc = level + 1e-9;
                    int64_t best = -1; double brc = INFINITY; int bon = 0;
                    if (len < max_depth) {
                        for (int64_t e = starts[x]; e < starts[x + 1]; e++) {
                            if (!alive[e]) continue;
                            int32_t y = V[e];
                            if (dead[y] || fabs(eta[y] - ex) > 1e-9) continue;
                            double rc = W[e] - ex + val[y] - val[x];
                            if (rc > lim_rc) continue;
                            if (rc < brc - 1e-9 || (rc < brc + 1e-9 && onpath[y] && !bon)) {
                                best = e; brc = rc; bon = onpath[y];
                            }
                        }
                    }
                    if (best < 0) { dead[x] = 1; onpath[x] = 0; len--; continue; }
                    int64_t y = V[best];
                    pedge[len - 1] = best;
                    if (!onpath[y]) { cum[len] = cum[len - 1] + brc; path[len++] = y; onpath[y] = 1; continue; }
                    int64_t i = len - 1;
                    while (path[i] != y) i--;
                    int64_t cl = len - i;
                    double sum = cum[len - 1] - cum[i] + brc;
                    if (cl <= max_len && sum <= frac * (cap - ex) * cl + 1e-7) {
                        if (no + cl > max_out) { full = 1; break; }
                        for (int64_t j = i; j < len; j++) { out_edges[no++] = pedge[j]; alive[pedge[j]] = 0; }
                        out_off[++nc] = no;
                        for (int64_t j = i + 1; j < len; j++) onpath[path[j]] = 0;
                        len = i + 1;                   /* continue from the cycle's first state */
                    } else {                           /* skip this closing edge, stay at x */
                        if (nd == dcap) { dcap *= 2; dropped = realloc(dropped, sizeof(int64_t) * dcap); }
                        dropped[nd++] = best; alive[best] = 0;
                    }
                }
                for (int64_t j = 0; j < len; j++) onpath[path[j]] = 0;
            }
        }
        for (int64_t j = 0; j < nd; j++) alive[dropped[j]] = 1;   /* skipped edges come back next level */
        nd = 0;
    }
    for (int64_t j = 0; j < no; j++) alive[out_edges[j]] = 1;
    free(dead); free(onpath); free(path); free(pedge); free(cum); free(dropped);
    return nc;
}

/* rc_select: out[e] = 1 for alive edges u->v with eta[u] == eta[v] <= cap and reduced cost
   W - eta[u] + val[v] - val[u] <= R (the subgraph the cycles of mean <= cap mostly live in).
   Returns the number of selected edges. */
int64_t rc_select(int64_t n, const int64_t *starts, const int32_t *V, const wt_t *W, const uint8_t *alive,
                  const double *eta, const double *val, double cap, double R, uint8_t *out)
{
    int64_t cnt = 0;
    for (int64_t u = 0; u < n; u++) {
        int64_t a = starts[u], b = starts[u + 1];
        double eu = eta[u];
        if (!(eu <= cap)) { memset(out + a, 0, b - a); continue; }
        for (int64_t e = a; e < b; e++) {
            out[e] = 0;
            if (!alive[e]) continue;
            int32_t v = V[e];
            if (fabs(eta[v] - eu) > 1e-9) continue;
            if (W[e] - eu + val[v] - val[u] <= R + 1e-9) { out[e] = 1; cnt++; }
        }
    }
    return cnt;
}

/* compact_subgraph: renumber the states with a selected out-edge (sel[e] != 0; the selection must be
   pruned, so every endpoint of a selected edge has one) to 0..ns-1 in index order and write the CSR
   of the selected edges: out_starts (ns+1), out_V, out_W, out_idx (original edge number).  map is an
   n-sized scratch array (on return map[u] = compact id or -1).  Returns ns. */
int64_t compact_subgraph(int64_t n, const int64_t *starts, const int32_t *V, const wt_t *W, const uint8_t *sel,
                         int32_t *map, int64_t *out_starts, int32_t *out_V, wt_t *out_W, int32_t *out_idx)
{
    int64_t ns = 0;
    for (int64_t u = 0; u < n; u++) {
        map[u] = -1;
        for (int64_t e = starts[u]; e < starts[u + 1]; e++) if (sel[e]) { map[u] = (int32_t)ns++; break; }
    }
    int64_t k = 0;
    for (int64_t u = 0; u < n; u++) {
        if (map[u] < 0) continue;
        out_starts[map[u]] = k;
        for (int64_t e = starts[u]; e < starts[u + 1]; e++) {
            if (!sel[e]) continue;
            out_V[k] = map[V[e]]; out_W[k] = W[e]; out_idx[k] = (int32_t)e; k++;
        }
    }
    out_starts[ns] = k;
    return ns;
}
