/* C helpers for lean_minimize.py: everything works on the source-sorted CSR arrays of
   LeanAutomaton.edges (starts int64[n+1], V int32[E], W uint8[E]); no per-edge temporaries.

   bf_jacobi   : the synchronous (Jacobi) Bellman-Ford of min_range.bf_bounded / refine_fast.bellman_ford,
                 iteration for iteration (same convergence and failure semantics), but each iteration only
                 relaxes the out-edges of states whose value changed in the previous one (the others cannot
                 lower anything: pi_t[v] <= pi_{t-1}[u] + w already).
   check_pot   : every edge q*w - p + pi[u] - pi[v] >= 0, 0 <= pi, and pi <= D + q*init (optional).
   removable   : minimize_fast.Blockers.removable without the per-edge count arrays: the blocker count
                 of (extension e, code) is the sum over window lengths c of per-(window shape, c) tables.
   dp_step     : one step of refine_fast.vertex_bound's min-plus dynamic programme.
*/
#include <stdint.h>
#include <string.h>

int64_t bf_jacobi(int64_t n, const int64_t *st, const int32_t *V, const uint8_t *W, int64_t p, int64_t q,
                  int32_t *pi, int32_t *nw, uint8_t *chg, int64_t max_iter, int neg_check, int64_t *iters)
{
    /* returns 0 converged (pi holds the fixpoint), -1 a value < 0 (neg_check), -2 cap, -3 overflow */
    int32_t *cur = pi, *nxt = nw;
    int64_t res = -2, it;
    memset(chg, 1, (size_t)n);
    for (it = 0; it < max_iter; it++) {
        memcpy(nxt, cur, (size_t)n * sizeof(int32_t));
        for (int64_t u = 0; u < n; u++) {
            if (!chg[u]) continue;
            int64_t base = (int64_t)cur[u] - p;
            for (int64_t e = st[u]; e < st[u + 1]; e++) {
                int64_t c = base + q * (int64_t)W[e];
                int32_t v = V[e];
                if (c < nxt[v]) {
                    if (c < INT32_MIN / 2) { res = -3; goto done; }
                    nxt[v] = (int32_t)c;
                }
            }
        }
        int any = 0, neg = 0;
        for (int64_t v = 0; v < n; v++) {
            uint8_t c = nxt[v] != cur[v];
            chg[v] = c; any |= c;
            neg |= nxt[v] < 0;
        }
        if (neg_check && neg) { res = -1; break; }
        if (!any) { res = 0; break; }
        int32_t *t = cur; cur = nxt; nxt = t;
    }
done:
    if (cur != pi) memcpy(pi, cur, (size_t)n * sizeof(int32_t));
    *iters = it;
    return res;
}

int64_t check_pot(int64_t n, const int64_t *st, const int32_t *V, const uint8_t *W, int64_t p, int64_t q,
                  const int32_t *pi, int use_ub, int64_t D, const int32_t *init, int64_t m1)
{
    /* number of violations: edges with negative reduced cost, states with pi < 0 or pi > D + q*init */
    int64_t bad = 0;
    for (int64_t u = 0; u < n; u++) {
        int64_t pu = pi[u];
        if (pu < 0) bad++;
        if (use_ub && pu > D + q * (int64_t)init[u % m1]) bad++;
        for (int64_t e = st[u]; e < st[u + 1]; e++)
            if (q * (int64_t)W[e] - p + pu - (int64_t)pi[V[e]] < 0) bad++;
    }
    return bad;
}

int removable(int64_t nx, const int32_t *exts, const uint8_t *ori, int64_t nlow, const int64_t *c0, int cc,
              int k, int64_t ns, int64_t m1, const int32_t *esrc, const int32_t *enxt,
              const int16_t *tab, const int64_t *toff_f, const int64_t *toff_r,
              const int32_t *rev, const int64_t *revoff, const int32_t *pi, int64_t p, int64_t q,
              int64_t *checked)
{
    int64_t pw[32];
    pw[0] = 1;
    for (int c = 1; c <= k; c++) pw[c] = pw[c - 1] * ns;
    const int32_t *revcc = rev + revoff[cc];
    int64_t nhi = pw[k - cc], step = pw[cc], chk = 0;
    for (int64_t j = 0; j < nx; j++) {
        int32_t e = exts[j];
        const int64_t *of = toff_f + (int64_t)e * (k + 1), *orr = toff_r + (int64_t)e * (k + 1);
        int64_t ubase = (int64_t)esrc[e] * m1, vbase = (int64_t)enxt[e] * m1;
        for (int64_t t = 0; t < nlow; t++) {
            for (int pass = 1; pass <= 2; pass++) {
                if (!(ori[j] & pass)) continue;
                int64_t low = pass == 1 ? c0[t] : revcc[c0[t]];
                if (pass == 2 && (ori[j] & 1) && low == c0[t]) continue;     /* palindrome: same codes */
                for (int64_t h = 0; h < nhi; h++) {
                    int64_t code = low + h * step;
                    int cnt = 0;
                    for (int c = k; c >= 2; c--) {
                        int64_t l = code % pw[c];
                        if (of[c] >= 0) cnt += tab[of[c] + l];
                        if (orr[c] >= 0) cnt += tab[orr[c] + rev[revoff[c] + l]];
                        if (cnt >= 2) break;
                    }
                    if (cnt != 1) continue;
                    chk++;
                    int64_t u = ubase + code / ns, v = vbase + code % m1, w = code % ns + 1;
                    if (q * w - p + (int64_t)pi[u] - (int64_t)pi[v] < 0) { *checked += chk; return 0; }
                }
            }
        }
    }
    *checked += chk;
    return 1;
}

int32_t dp_step(int64_t n, const int64_t *st, const int32_t *V, const uint8_t *W,
                const int32_t *dp, int32_t *out)
{
    /* out[v] = min over edges u->v of dp[u] + W (INT32_MAX = inf); returns min(out) */
    for (int64_t v = 0; v < n; v++) out[v] = INT32_MAX;
    for (int64_t u = 0; u < n; u++) {
        if (dp[u] == INT32_MAX) continue;
        for (int64_t e = st[u]; e < st[u + 1]; e++) {
            int32_t c = dp[u] + (int32_t)W[e];
            if (c < out[V[e]]) out[V[e]] = c;
        }
    }
    int32_t m = INT32_MAX;
    for (int64_t v = 0; v < n; v++) if (out[v] < m) m = out[v];
    return m;
}
