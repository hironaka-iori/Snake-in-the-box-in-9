/* Count induced linear forests (induced subgraphs with max degree <= 2 and no cycle) of Q_n, n <= 5,
 * by number of vertices. Usage: forests N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N, NV; static int deg[64]; static int in[64]; static int uf[64];
static long long cnt[65]; static long long total;
static int find(int x) { while (uf[x] != x) x = uf[x]; return x; }
static void rec(int v, int size) {
    if (v == NV) { cnt[size]++; total++; return; }
    rec(v + 1, size); /* exclude v */
    /* include v: neighbours already decided are < v */
    int nb[8], c = 0;
    for (int k = 0; k < N; k++) { int w = v ^ (1 << k); if (w < v && in[w]) nb[c++] = w; }
    if (c > 2) return;
    for (int i = 0; i < c; i++) if (deg[nb[i]] >= 2) return;
    /* acyclicity: neighbours must be in different components (union-find without path compression) */
    int saved_parent[2], saved_root[2], ns = 0;
    if (c == 2 && find(nb[0]) == find(nb[1])) return;
    in[v] = 1; uf[v] = v; for (int i = 0; i < c; i++) deg[nb[i]]++; deg[v] = c;
    for (int i = 0; i < c; i++) { int r = find(nb[i]); saved_root[ns] = r; saved_parent[ns] = uf[r]; ns++; uf[r] = v; }
    rec(v + 1, size + 1);
    for (int i = ns - 1; i >= 0; i--) uf[saved_root[i]] = saved_parent[i];
    for (int i = 0; i < c; i++) deg[nb[i]]--; in[v] = 0; deg[v] = 0;
}
int main(int argc, char **argv) {
    N = atoi(argv[1]); NV = 1 << N;
    rec(0, 0);
    printf("{\"n\":%d,\"total\":%lld,\"by_size\":[", N, total);
    for (int s = 0; s <= NV; s++) printf("%s%lld", s ? "," : "", cnt[s]);
    printf("]}\n");
    return 0;
}
