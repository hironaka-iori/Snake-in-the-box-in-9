// Unit propagation probe for B229 first-cut selection.
//   up F.cnf parent                 parent fixpoint stats (JSON) + top short-clause occurrence counts
//   up F.cnf probe v1 v2 ...        for each var v: stats after +v and after -v (from the parent fixpoint)
// Stats: conflict, assigned vars, remaining clauses (not satisfied, >=1 free literal), remaining vars
// (free vars occurring in remaining clauses), remaining short clauses (free length 2 / 3).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static int nv, nc, *lits, *start, *len;
static signed char *val;            // val[v] in {-1,0,1}
static int *trail, ntrail;
static int **watch, *wn, *wcap;     // watch lists per literal index
static inline int li(int l) { return l > 0 ? 2 * l : -2 * l + 1; }
static inline int lval(int l) { int v = val[abs(l)]; return l > 0 ? v : -v; }
static void addw(int l, int c) { int i = li(l); if (wn[i] == wcap[i]) { wcap[i] = wcap[i] ? 2 * wcap[i] : 4; watch[i] = realloc(watch[i], wcap[i] * sizeof(int)); } watch[i][wn[i]++] = c; }
static int assign(int l) { if (lval(l) == 1) return 1; if (lval(l) == -1) return 0; val[abs(l)] = l > 0 ? 1 : -1; trail[ntrail++] = l; return 1; }
static int qhead;
static int propagate(void) {   // returns 0 on conflict
  while (qhead < ntrail) {
    int l = -trail[qhead++]; int i = li(l);   // literal l became false
    int *w = watch[i]; int n = wn[i], j = 0;
    for (int k = 0; k < n; k++) {
      int c = w[k]; int *cl = lits + start[c];
      if (len[c] == 1) { w[j++] = c; continue; }
      if (cl[0] == l) { int t = cl[0]; cl[0] = cl[1]; cl[1] = t; }
      if (lval(cl[0]) == 1) { w[j++] = c; continue; }
      int found = 0;
      for (int m = 2; m < len[c]; m++) if (lval(cl[m]) != -1) { int t = cl[1]; cl[1] = cl[m]; cl[m] = t; addw(cl[1], c); found = 1; break; }
      if (found) continue;
      w[j++] = c;
      if (lval(cl[0]) == -1) { for (k++; k < n; k++) w[j++] = w[k]; wn[i] = j; return 0; }
      assign(cl[0]);
    }
    wn[i] = j;
  }
  return 1;
}
static void undo(int to) { while (ntrail > to) val[abs(trail[--ntrail])] = 0; qhead = to; }
static int *seen;
static void stats(int conflict, const char *tag) {
  long rc = 0, r2 = 0, r3 = 0, rv = 0;
  if (!conflict) {
    memset(seen, 0, (nv + 1) * sizeof(int));
    for (int c = 0; c < nc; c++) {
      int sat = 0, fr = 0; int *cl = lits + start[c];
      for (int m = 0; m < len[c]; m++) { int v = lval(cl[m]); if (v == 1) { sat = 1; break; } if (v == 0) fr++; }
      if (sat || !fr) continue;
      rc++; if (fr == 2) r2++; if (fr == 3) r3++;
      for (int m = 0; m < len[c]; m++) if (!lval(cl[m]) && !seen[abs(cl[m])]) { seen[abs(cl[m])] = 1; rv++; }
    }
  }
  printf("{\"tag\": \"%s\", \"conflict\": %s, \"assigned\": %d, \"rem_clauses\": %ld, \"rem_vars\": %ld, \"rem_bin\": %ld, \"rem_ter\": %ld}\n",
         tag, conflict ? "true" : "false", ntrail, rc, rv, r2, r3);
  fflush(stdout);
}
int main(int argc, char **argv) {
  clock_t t0 = clock();
  FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
  if (fscanf(f, " p cnf %d %d", &nv, &nc) != 2) { fprintf(stderr, "bad header\n"); return 1; }
  long cap = 16L * nc, nl = 0; lits = malloc(cap * sizeof(int)); start = malloc(nc * sizeof(int)); len = malloc(nc * sizeof(int));
  int x, c = 0; start[0] = 0; int cur = 0;
  while (fscanf(f, "%d", &x) == 1) {
    if (nl == cap) { cap *= 2; lits = realloc(lits, cap * sizeof(int)); }
    if (x) { lits[nl++] = x; cur++; } else { len[c] = cur; c++; if (c < nc) start[c] = nl; cur = 0; }
  }
  fclose(f);
  if (c != nc) { fprintf(stderr, "clause count %d != header %d\n", c, nc); return 1; }
  fprintf(stderr, "read %d vars %d clauses %ld lits in %.1f s\n", nv, nc, nl, (double)(clock() - t0) / CLOCKS_PER_SEC);
  val = calloc(nv + 1, 1); trail = malloc((nv + 1) * sizeof(int)); seen = calloc(nv + 1, sizeof(int));
  watch = calloc(2 * nv + 2, sizeof(int *)); wn = calloc(2 * nv + 2, sizeof(int)); wcap = calloc(2 * nv + 2, sizeof(int));
  int conflict = 0;
  for (int k = 0; k < nc; k++) {
    if (len[k] == 0) conflict = 1;
    else if (len[k] == 1) { if (!assign(lits[start[k]])) conflict = 1; }
    else { addw(lits[start[k]], k); addw(lits[start[k] + 1], k); }
  }
  if (!conflict && !propagate()) conflict = 1;
  clock_t t1 = clock();
  stats(conflict, "parent");
  fprintf(stderr, "parent UP %.1f s\n", (double)(clock() - t1) / CLOCKS_PER_SEC);
  if (conflict) return 0;
  int base = ntrail;
  if (argc > 2 && !strcmp(argv[2], "parent")) {   // occurrence counts of free vars in remaining clauses of free length <= 3
    int *occ = calloc(nv + 1, sizeof(int));
    for (int k = 0; k < nc; k++) {
      int sat = 0, fr = 0; int *cl = lits + start[k];
      for (int m = 0; m < len[k]; m++) { int v = lval(cl[m]); if (v == 1) { sat = 1; break; } if (v == 0) fr++; }
      if (sat || fr < 2 || fr > 3) continue;
      for (int m = 0; m < len[k]; m++) if (!lval(cl[m])) occ[abs(cl[m])]++;
    }
    // print all vars with occ > 0 as "OCC v count" lines (caller ranks)
    for (int v = 1; v <= nv; v++) if (occ[v]) printf("OCC %d %d\n", v, occ[v]);
    return 0;
  }
  for (int a = 3; a < argc; a++) {
    int v = atoi(argv[a]); char tag[64];
    for (int s = 1; s >= -1; s -= 2) {
      int l = s * v; snprintf(tag, sizeof tag, "%d", l);
      clock_t ts = clock();
      int ok = lval(l) == -1 ? 0 : (assign(l), propagate());
      stats(!ok, tag);
      fprintf(stderr, "probe %d: %.2f s\n", l, (double)(clock() - ts) / CLOCKS_PER_SEC);
      undo(base);
    }
  }
  return 0;
}
