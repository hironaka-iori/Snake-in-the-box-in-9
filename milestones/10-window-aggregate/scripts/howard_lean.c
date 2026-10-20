/* Howard policy iteration for the minimum cycle mean (same rules as refine_fast.howard).
   Graph in CSR form by source: edges starts[u] .. starts[u+1]-1 go to V[e] with weight W[e].
   alive[e] != 0 marks usable edges (the caller deletes edges to extract further cycles).
   pol[u] is an edge index (or -1) on input (warm start) and output.
   howard_run takes double weights, howard_run_u8 uint8 weights (same code).
   Build: cc -O2 -shared -fPIC -o howard_c.so howard_c.c */
#include <stdint.h>
#include <stdlib.h>
#include <math.h>

#define HOWARD_BODY(NAME, WT) \
int NAME(int64_t n, const int64_t *starts, const int32_t *V, const WT *W, \
               const uint8_t *alive, int64_t *pol, double *eta, double *val, int iters) \
{ \
    int8_t *state = malloc(n); \
    int64_t *path = malloc(sizeof(int64_t) * (n + 1)); \
    int it; \
    /* repair the policy: it must use an alive edge */ \
    for (int64_t u = 0; u < n; u++) { \
        int64_t p = pol[u]; \
        if (p < starts[u] || p >= starts[u + 1] || !alive[p]) { \
            pol[u] = -1; \
            for (int64_t e = starts[u]; e < starts[u + 1]; e++) if (alive[e]) { pol[u] = e; break; } \
        } \
    } \
    for (it = 0; it < iters; it++) { \
        for (int64_t u = 0; u < n; u++) { state[u] = 0; eta[u] = INFINITY; val[u] = 0.0; } \
        for (int64_t s0 = 0; s0 < n; s0++) { \
            if (state[s0] || pol[s0] < 0) continue; \
            int64_t len = 0, x = s0; \
            while (x >= 0 && state[x] == 0) { \
                state[x] = 1; path[len++] = x; \
                x = pol[x] >= 0 ? V[pol[x]] : -1; \
            } \
            int64_t tail_end = len;               /* path[0 .. tail_end-1] is the tail */ \
            if (x >= 0 && state[x] == 1) { \
                int64_t i = 0; \
                while (path[i] != x) i++; \
                double s = 0.0; \
                for (int64_t j = i; j < len; j++) s += W[pol[path[j]]]; \
                double mu = s / (double)(len - i); \
                for (int64_t j = i; j < len; j++) eta[path[j]] = mu; \
                val[x] = 0.0; \
                for (int64_t j = len - 1; j > i; j--) { \
                    int64_t y = path[j]; \
                    val[y] = W[pol[y]] - mu + val[V[pol[y]]]; \
                } \
                tail_end = i; \
            } \
            for (int64_t j = tail_end - 1; j >= 0; j--) { \
                int64_t y = path[j]; \
                if (pol[y] < 0) continue; \
                int64_t z = V[pol[y]]; \
                if (isfinite(eta[z])) { eta[y] = eta[z]; val[y] = W[pol[y]] - eta[y] + val[z]; } \
            } \
            for (int64_t j = 0; j < len; j++) state[path[j]] = 2; \
        } \
        int changed = 0; \
        for (int64_t u = 0; u < n; u++) { \
            if (pol[u] < 0) continue; \
            int64_t be = -1; double bet = INFINITY; \
            for (int64_t e = starts[u]; e < starts[u + 1]; e++) { \
                if (!alive[e]) continue; \
                double t = eta[V[e]]; \
                if (t < bet) { bet = t; be = e; } \
            } \
            if (be >= 0 && bet < eta[u] - 1e-9) { pol[u] = be; changed = 1; continue; } \
            if (!isfinite(eta[u])) continue; \
            int64_t bv = -1; double bval = INFINITY; \
            for (int64_t e = starts[u]; e < starts[u + 1]; e++) { \
                if (!alive[e]) continue; \
                double t = eta[V[e]]; \
                if (fabs(t - eta[u]) < 1e-9) { \
                    double v2 = W[e] - t + val[V[e]]; \
                    if (v2 < bval) { bval = v2; bv = e; } \
                } \
            } \
            if (bv >= 0 && bval < val[u] - 1e-9) { pol[u] = bv; changed = 1; } \
        } \
        if (!changed) break; \
    } \
    free(state); free(path); \
    return it; \
}

HOWARD_BODY(howard_run, double)
HOWARD_BODY(howard_run_u8, uint8_t)
