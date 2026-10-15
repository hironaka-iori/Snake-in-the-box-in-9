/* Exhaustive bitset DFS for snake-in-the-box extensions in Q_n (n <= 9).
 *
 * Input (stdin): one snake per line, "k v0 v1 ... v{k-1}" (vertex integers).
 *
 * Modes
 *   regrow  N KEEP TARGET NODES [LAYERBIT]
 *       Keep the first KEEP vertices (both orientations are tried), then search
 *       exhaustively for an induced extension reaching TARGET vertices.  Reports
 *       the longest extension seen and whether the subtree was exhausted.  With
 *       LAYERBIT >= 0 the new vertices must agree with the head on that bit
 *       (single-crossing partner model).
 *   window  N W TRIES MAXALT NODES SEED
 *       Random internal windows of W deleted vertices.  Enumerates induced
 *       replacements between the two fixed ends whose length is >= the original
 *       (equal-length ones are printed as plateau moves, +2 ones as records).
 *
 * Output: one JSON object per line.  All found paths are re-verified in O(k^2)
 * before printing.  This program is experimental search code; its INFEASIBLE
 * outcomes are not certificates.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXV 512
#define W64 8
typedef struct { uint64_t w[W64]; } bs;

static int N, NV;
static bs NB[MAXV], CN[MAXV]; /* open / closed neighbourhoods */
static bs PAR[2];             /* vertices of even / odd weight */
static int use_peel = 1;      /* SNAKE_NO_PEEL=1 disables the leaf-peeling bound */
static int count_only = 0;    /* SNAKE_COUNT_ONLY=1: bound = reachable count (the Lean-checked bound) */
static long long enum_cap, enum_count;

static inline void bs_clear(bs *a) { memset(a, 0, sizeof *a); }
static inline void bs_set(bs *a, int v) { a->w[v >> 6] |= 1ULL << (v & 63); }
static inline int bs_has(const bs *a, int v) { return (a->w[v >> 6] >> (v & 63)) & 1; }
static inline void bs_or(bs *a, const bs *b) { for (int i = 0; i < W64; i++) a->w[i] |= b->w[i]; }
static inline int bs_count_and(const bs *a, const bs *b) {
    int c = 0;
    for (int i = 0; i < W64; i++) c += __builtin_popcountll(a->w[i] & b->w[i]);
    return c;
}

static void init_cube(int n) {
    N = n; NV = 1 << n;
    bs_clear(&PAR[0]); bs_clear(&PAR[1]);
    for (int v = 0; v < NV; v++) {
        bs_clear(&NB[v]);
        for (int k = 0; k < n; k++) bs_set(&NB[v], v ^ (1 << k));
        CN[v] = NB[v]; bs_set(&CN[v], v);
        bs_set(&PAR[__builtin_popcount(v) & 1], v);
    }
}

static int verify_path(const int *p, int k) {
    for (int i = 0; i < k; i++)
        for (int j = i + 1; j < k; j++) {
            int d = __builtin_popcount(p[i] ^ p[j]);
            if (d == 0) return 0;
            if ((d == 1) != (j == i + 1)) return 0;
        }
    return 1;
}

static void print_path(const char *tag, const int *p, int k, const char *extra) {
    printf("{\"event\":\"%s\",\"vertices\":%d,\"edges\":%d,\"verified\":%s%s,\"path\":[",
           tag, k, k - 1, verify_path(p, k) ? "true" : "false", extra ? extra : "");
    for (int i = 0; i < k; i++) printf("%s%d", i ? "," : "", p[i]);
    printf("]}\n");
    fflush(stdout);
}

/* ---- upper bound: reachable free region from head, with parity alternation ---- */
static int region_bound(int head, const bs *ban, const bs *allowed, int *goal_reach, int goal) {
    /* BFS from neighbours of head inside free = allowed & ~ban. */
    static int queue[MAXV];
    bs seen; bs_clear(&seen);
    int qh = 0, qt = 0;
    for (int k = 0; k < N; k++) {
        int u = head ^ (1 << k);
        if (bs_has(ban, u) || !bs_has(allowed, u) || bs_has(&seen, u)) continue;
        bs_set(&seen, u); queue[qt++] = u;
    }
    while (qh < qt) {
        int u = queue[qh++];
        for (int k = 0; k < N; k++) {
            int x = u ^ (1 << k);
            if (bs_has(&seen, x) || bs_has(ban, x) || !bs_has(allowed, x)) continue;
            bs_set(&seen, x); queue[qt++] = x;
        }
    }
    if (goal_reach) *goal_reach = goal >= 0 && bs_has(&seen, goal);
    int p = __builtin_popcount(head) & 1;
    int opp = bs_count_and(&seen, &PAR[p ^ 1]); /* first new vertex has opposite parity */
    int same = bs_count_and(&seen, &PAR[p]);
    int a = opp < same + 1 ? opp : same + 1;
    int b = same < opp ? same : opp;
    int parity_bound = a + b;
    if (count_only) return qt;
    if (!use_peel || qt == 0) return parity_bound;
    /* Leaf peeling: a vertex of degree <= 1 inside seen+{head} hangs off the rest by at
       most one edge, so a path that enters its tree must end there.  Hence the path uses
       at most (core vertices) + (deepest hanging tree height) new vertices. */
    static int deg[MAXV], round_of[MAXV], peel[MAXV];
    bs region = seen; bs_set(&region, head);
    int ph = 0, pt = 0;
    for (int i = 0; i < qt; i++) {
        int u = queue[i], d = 0;
        for (int k = 0; k < N; k++) d += bs_has(&region, u ^ (1 << k));
        deg[u] = d; round_of[u] = 0;
        if (d <= 1) { round_of[u] = 1; peel[pt++] = u; }
    }
    int removed = 0, maxround = 0;
    while (ph < pt) {
        int u = peel[ph++];
        removed++;
        if (round_of[u] > maxround) maxround = round_of[u];
        for (int k = 0; k < N; k++) {
            int x = u ^ (1 << k);
            if (x == head || !bs_has(&seen, x) || round_of[x]) continue;
            if (--deg[x] <= 1) { round_of[x] = round_of[u] + 1; peel[pt++] = x; }
        }
    }
    int peel_bound = (qt - removed) + maxround;
    return peel_bound < parity_bound ? peel_bound : parity_bound;
}

/* ---------------------------------- regrow ---------------------------------- */
static int path[MAXV], best_path[MAXV];
static int plen, best_len, target_len;
static long long nodes, node_limit;
static int aborted, found;
static bs allowed_g;

static void dfs_regrow(bs ban) {
    if (found || aborted) return;
    if (++nodes > node_limit) { aborted = 1; return; }
    if (plen > best_len) { best_len = plen; memcpy(best_path, path, sizeof(int) * plen); }
    if (plen >= target_len) {
        best_len = plen; memcpy(best_path, path, sizeof(int) * plen);
        if (enum_cap > 0) { /* SNAKE_ENUM=cap: print every completion, stop after cap */
            print_path("solution", path, plen, NULL);
            if (++enum_count >= enum_cap) found = 1;
            return;
        }
        found = 1; return;
    }
    int head = path[plen - 1];
    int ub = region_bound(head, &ban, &allowed_g, NULL, -1);
    if (plen + ub < target_len) return;
    bs nb = ban; bs_or(&nb, &CN[head]);
    for (int k = 0; k < N; k++) {
        int x = head ^ (1 << k);
        if (bs_has(&ban, x) || !bs_has(&allowed_g, x)) continue;
        path[plen++] = x;
        dfs_regrow(nb);
        plen--;
        if (found || aborted) return;
    }
}

static void run_regrow(int *s, int k, int keep, int layerbit, int idx, int rev) {
    if (keep > k) keep = k;
    bs ban; bs_clear(&ban);
    for (int i = 0; i < keep; i++) {
        path[i] = s[i];
        if (i < keep - 1) bs_or(&ban, &CN[s[i]]);
    }
    bs_set(&ban, s[keep - 1]);
    plen = keep; best_len = keep; memcpy(best_path, path, sizeof(int) * keep);
    nodes = 0; aborted = 0; found = 0;
    bs_clear(&allowed_g);
    int head = s[keep - 1];
    for (int v = 0; v < NV; v++)
        if (layerbit < 0 || ((v >> layerbit) & 1) == ((head >> layerbit) & 1)) bs_set(&allowed_g, v);
    dfs_regrow(ban);
    const char *status = found ? "FOUND" : aborted ? "UNKNOWN" : "INFEASIBLE";
    printf("{\"event\":\"regrow\",\"index\":%d,\"reversed\":%d,\"keep\":%d,\"target\":%d,"
           "\"status\":\"%s\",\"best_vertices\":%d,\"nodes\":%lld}\n",
           idx, rev, keep, target_len, status, best_len, nodes);
    fflush(stdout);
    if (found) print_path("record", best_path, best_len, NULL);
}

/* ---------------------------------- window ---------------------------------- */
static int wgoal, wmin_len, wmax_alt, walt, wfound_long;
static int *wsnake, wk, wi, wj; /* keep [0..wi] and [wj..wk-1] */
static int wpath[MAXV], wplen;
/* combo mode: each accepted filling of the truncated snake is followed by end regrowth */
static int combo_mode, combo_unknown, combo_found;
static long long combo_rnodes, combo_nodes_used;

static void emit_window(void) {
    int out[MAXV], m = 0;
    for (int i = 0; i <= wi; i++) out[m++] = wsnake[i];
    for (int i = 1; i < wplen; i++) out[m++] = wpath[i]; /* wpath[0] = wsnake[wi] */
    for (int i = wj; i < wk; i++) out[m++] = wsnake[i];
    if (combo_mode) {
        long long saved_nodes = nodes, saved_limit = node_limit;
        int saved_aborted = aborted;
        /* regrow from the end of the modified, truncated snake */
        bs ban; bs_clear(&ban);
        for (int i = 0; i < m; i++) { path[i] = out[i]; if (i < m - 1) bs_or(&ban, &CN[out[i]]); }
        bs_set(&ban, out[m - 1]);
        plen = m; best_len = m; found = 0; aborted = 0; nodes = 0; node_limit = combo_rnodes;
        dfs_regrow(ban);
        combo_nodes_used += nodes;
        if (aborted) combo_unknown++;
        if (found) {
            combo_found++;
            char extra[128];
            snprintf(extra, sizeof extra, ",\"window\":[%d,%d],\"old_gap\":%d,\"new_gap\":%d,\"cut\":%d", wi, wj, wj - wi, wplen, wk);
            print_path("record", best_path, best_len, extra);
        }
        nodes = saved_nodes; node_limit = saved_limit; aborted = saved_aborted;
        return;
    }
    char extra[96];
    snprintf(extra, sizeof extra, ",\"window\":[%d,%d],\"old_gap\":%d,\"new_gap\":%d", wi, wj, wj - wi, wplen);
    print_path(m > wk ? "record" : "plateau", out, m, extra);
}

static void dfs_window(bs ban) {
    if (aborted || walt >= wmax_alt) return;
    if (++nodes > node_limit) { aborted = 1; return; }
    int head = wpath[wplen - 1];
    /* wplen counts wpath[0]=a; the gap length if we close now is wplen (edges a..head..b) */
    if (bs_has(&NB[head], wgoal) && wplen > 1) {
        if (wplen >= wmin_len) {
            int gap_edges = wplen; /* edges = (wplen-1) internal steps + 1 to goal */
            if (gap_edges > wj - wi) wfound_long = 1;
            walt++; emit_window();
        }
        return; /* head is adjacent to b: must close here (induced) */
    }
    int ub = region_bound(head, &ban, &allowed_g, NULL, -1);
    if (wplen + ub < wmin_len) return;
    bs nb = ban; bs_or(&nb, &CN[head]);
    for (int k = 0; k < N; k++) {
        int x = head ^ (1 << k);
        if (bs_has(&ban, x) || x == wgoal) continue;
        wpath[wplen++] = x;
        dfs_window(nb);
        wplen--;
        if (aborted || walt >= wmax_alt) return;
    }
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rng(void) { rng_state ^= rng_state << 13; rng_state ^= rng_state >> 7; rng_state ^= rng_state << 17; return rng_state; }

static void run_window(int *s, int k, int w, int slack, int tries, int idx) {
    for (int t = 0; t < tries; t++) {
        if (k - w - 2 <= 0) return;
        int i = 1 + (int)(rng() % (uint64_t)(k - w - 2)); /* keep s[i], s[i+w+1] */
        int j = i + w + 1;
        wsnake = s; wk = k; wi = i; wj = j;
        bs ban; bs_clear(&ban);
        for (int q = 0; q < k; q++) {
            if (q > i && q < j) continue;
            if (q == i || q == j) { bs_set(&ban, s[q]); continue; }
            bs_or(&ban, &CN[s[q]]);
        }
        /* a's other neighbours are banned once the DFS leaves a; a neighbour of b
           forces the gap to close there (see dfs_window). */
        bs_clear(&allowed_g);
        for (int v = 0; v < NV; v++) bs_set(&allowed_g, v);
        wpath[0] = s[i]; wplen = 1; wgoal = s[j]; wmin_len = j - i - 2 * slack; walt = 0; wfound_long = 0;
        nodes = 0; aborted = 0; combo_unknown = 0; combo_found = 0; combo_nodes_used = 0;
        dfs_window(ban);
        printf("{\"event\":\"window\",\"index\":%d,\"window\":[%d,%d],\"cut\":%d,\"alternatives\":%d,"
               "\"longer\":%d,\"status\":\"%s\",\"nodes\":%lld,\"regrow_unknown\":%d,"
               "\"regrow_found\":%d,\"regrow_nodes\":%lld}\n",
               idx, i, j, k, walt, wfound_long, aborted ? "UNKNOWN" : (walt >= wmax_alt ? "CAPPED" : "EXHAUSTED"),
               nodes, combo_unknown, combo_found, combo_nodes_used);
        fflush(stdout);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 2; }
    const char *mode = argv[1];
    init_cube(atoi(argv[2]));
    if (getenv("SNAKE_NO_PEEL")) use_peel = 0;
    if (getenv("SNAKE_COUNT_ONLY")) count_only = 1;
    if (getenv("SNAKE_ENUM")) enum_cap = atoll(getenv("SNAKE_ENUM"));
    static int s[MAXV], r[MAXV];
    int k, idx = 0;
    while (scanf("%d", &k) == 1) {
        for (int i = 0; i < k; i++) if (scanf("%d", &s[i]) != 1) return 3;
        if (!verify_path(s, k)) { fprintf(stderr, "input %d is not a snake\n", idx); return 4; }
        if (!strcmp(mode, "regrow")) {
            int keep = atoi(argv[3]); target_len = atoi(argv[4]); node_limit = atoll(argv[5]);
            int layerbit = argc > 6 ? atoi(argv[6]) : -1;
            int forward_only = argc > 7 && atoi(argv[7]);
            run_regrow(s, k, keep, layerbit, idx, 0);
            if (forward_only) { idx++; continue; }
            for (int i = 0; i < k; i++) r[i] = s[k - 1 - i];
            run_regrow(r, k, keep, layerbit, idx, 1);
        } else if (!strcmp(mode, "window")) {
            int w = atoi(argv[3]), tries = atoi(argv[4]);
            wmax_alt = atoi(argv[5]); node_limit = atoll(argv[6]);
            rng_state ^= (uint64_t)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL + (uint64_t)idx;
            run_window(s, k, w, 0, tries, idx);
        } else if (!strcmp(mode, "combo")) {
            /* combo N W SLACK CUT TARGET TRIES WNODES RNODES SEED (forward orientation only) */
            int w = atoi(argv[3]), slack = atoi(argv[4]), cut = atoi(argv[5]);
            target_len = atoi(argv[6]);
            int tries = atoi(argv[7]);
            node_limit = atoll(argv[8]); combo_rnodes = atoll(argv[9]);
            rng_state ^= (uint64_t)atoll(argv[10]) * 0x9E3779B97F4A7C15ULL + (uint64_t)idx;
            combo_mode = 1; wmax_alt = 1 << 30;
            run_window(s, cut < k ? cut : k, w, slack, tries, idx);
        }
        idx++;
    }
    return 0;
}
