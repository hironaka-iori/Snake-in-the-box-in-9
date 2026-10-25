/* Longest concrete unrolling of a cyclic walk of direction shapes in Q9.

   Input (argv): p  w0..w6  r_0 .. r_{p-1}  [nodelimit]
     p       period (number of automaton transitions per period)
     w0..w6  the canonical 7-direction shape of the start state (labels < 9)
     r_i     rule of transition i: 0 = fresh (new direction differs from the previous 6, i.e. the new 7-window
             has a new label; it may equal the direction 7 back),
             d in 1..6 = the new direction repeats the direction d steps back.
   The concrete sequence x_0..x_{6+n} starts with x_0..x_6 = w (wlog by a coordinate
   permutation); transition t (1-based) appends x_{6+t} by rule r_{(t-1) mod p}.
   The vertices v_0 = 0, v_{i+1} = v_i ^ (1 << x_i) must form an induced path of Q9.

   Exhaustive DFS over the fresh choices, with the symmetry that labels never used so far
   are interchangeable (only the smallest one is tried).  Prints the maximum number of
   transitions n (and the path length 7 + n edges), the number of DFS nodes and one
   maximum sequence.  A node limit makes the answer a lower bound (flagged). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXL 600
static int p, rule[4096], x[MAXL], best = -1, bestx[MAXL];
static unsigned char inpath[512];
static int v[MAXL];
static long long nodes = 0, limit = 0;
static int aborted = 0;
static int usedcnt[9];

static int can_add(int len, int d) {
    /* path has edges x_0..x_{len-1}, endpoint v[len]; add edge d */
    int w = v[len] ^ (1 << d);
    if (inpath[w]) return 0;
    for (int k = 0; k < 9; k++) {
        int u = w ^ (1 << k);
        if (u != v[len] && inpath[u]) return 0;
    }
    return 1;
}

static void push(int len, int d) {
    x[len] = d; v[len + 1] = v[len] ^ (1 << d); inpath[v[len + 1]] = 1; usedcnt[d]++;
}
static void pop(int len) { inpath[v[len + 1]] = 0; usedcnt[x[len]]--; }

static void dfs(int len) {  /* len = number of edges so far (>= 7) */
    nodes++;
    if (limit && nodes > limit) { aborted = 1; return; }
    int n = len - 7;
    if (n > best) { best = n; memcpy(bestx, x, sizeof(int) * len); }
    if (len >= MAXL - 1) return;
    int r = rule[n % p];
    if (r > 0) {
        int d = x[len - r];
        if (can_add(len, d)) { push(len, d); dfs(len + 1); pop(len); }
        return;
    }
    int recent = 0;
    for (int k = 1; k <= 6; k++) recent |= 1 << x[len - k];
    int triedfresh = 0;
    for (int d = 0; d < 9; d++) {
        if (recent >> d & 1) continue;
        if (usedcnt[d] == 0) { if (triedfresh) continue; triedfresh = 1; }
        if (can_add(len, d)) { push(len, d); dfs(len + 1); pop(len); if (aborted) return; }
    }
}

int main(int argc, char **argv) {
    p = atoi(argv[1]);
    int w[7];
    for (int i = 0; i < 7; i++) w[i] = atoi(argv[2 + i]);
    for (int i = 0; i < p; i++) rule[i] = atoi(argv[9 + i]);
    if (argc > 9 + p) limit = atoll(argv[9 + p]);
    v[0] = 0; inpath[0] = 1;
    for (int i = 0; i < 7; i++) {
        if (!can_add(i, w[i])) { printf("start window not induced\n"); return 1; }
        push(i, w[i]);
    }
    dfs(7);
    printf("{\"max_transitions\": %d, \"path_edges\": %d, \"nodes\": %lld, \"exhaustive\": %s, \"seq\": [",
           best, best + 7, nodes, aborted ? "false" : "true");
    for (int i = 0; i < best + 7; i++) printf("%s%d", i ? ", " : "", bestx[i]);
    printf("]}\n");
    return 0;
}
