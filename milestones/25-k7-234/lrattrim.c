/* Streaming LRAT trimmer: lrattrim NCL PROOF [CORE_OUT]
   Reads a text LRAT proof (CaDiCaL --lrat --no-binary; may be a FIFO), keeps every addition
   line's hints in memory, and walks back from the empty clause.  Prints
   "lemmas hints core" of the cone of the empty clause; with CORE_OUT writes the original clause
   ids it uses (one per line, increasing).  No proof is ever stored on disk. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static int *H; static ll nH, cH;           /* all hints */
static ll *off; static ll cOff;            /* per lemma (id - ncl - 1): start in H, -1 = none; end = off of next added */
static ll *endo;
static void push(int h) { if (nH == cH) { cH = cH ? 2 * cH : 1 << 20; H = realloc(H, cH * sizeof(int)); if (!H) { fprintf(stderr, "oom\n"); exit(2); } } H[nH++] = h; }
int main(int argc, char **argv) {
    if (argc < 3) return 1;
    ll ncl = atoll(argv[1]);
    FILE *f = fopen(argv[2], "r"); if (!f) { perror(argv[2]); return 1; }
    static char buf[1 << 16]; setvbuf(f, NULL, _IOFBF, 1 << 22);
    ll last = -1;
    int c = 0;
    /* tokenizer over chars */
    for (;;) {
        ll id = 0; int got = 0;
        c = getc_unlocked(f);
        while (c == ' ' || c == '\n' || c == '\r') c = getc_unlocked(f);
        if (c == EOF) break;
        while (c >= '0' && c <= '9') { id = id * 10 + (c - '0'); c = getc_unlocked(f); got = 1; }
        if (!got) { while (c != '\n' && c != EOF) c = getc_unlocked(f); continue; }
        while (c == ' ') c = getc_unlocked(f);
        if (c == 'd') { while (c != '\n' && c != EOF) c = getc_unlocked(f); continue; }
        /* literals until 0 */
        int nlit = 0;
        for (;;) {
            while (c == ' ') c = getc_unlocked(f);
            int neg = 0; ll v = 0;
            if (c == '-') { neg = 1; c = getc_unlocked(f); }
            while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = getc_unlocked(f); }
            if (v == 0) break;
            nlit++; (void)neg;
        }
        ll k = id - ncl - 1;
        if (k < 0) { fprintf(stderr, "bad id\n"); return 3; }
        if (k >= cOff) { ll n = cOff ? cOff : 1 << 16; while (n <= k) n *= 2; off = realloc(off, n * sizeof(ll)); endo = realloc(endo, n * sizeof(ll)); for (ll j = cOff; j < n; j++) off[j] = -1; cOff = n; }
        off[k] = nH;
        for (;;) {
            while (c == ' ') c = getc_unlocked(f);
            int neg = 0; ll v = 0;
            if (c == '-') { neg = 1; c = getc_unlocked(f); }
            while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = getc_unlocked(f); }
            if (v == 0) break;
            if (neg) { fprintf(stderr, "RAT\n"); return 4; }
            push((int)v);
        }
        endo[k] = nH;
        while (c != '\n' && c != EOF) c = getc_unlocked(f);
        if (nlit == 0) { last = id; break; }
    }
    /* drain the rest (FIFO writer must not block) */
    while (fread(buf, 1, sizeof buf, f) > 0) ;
    fclose(f);
    if (last < 0) { printf("-1 -1 -1\n"); return 5; }
    char *need = calloc(cOff + 1, 1);
    char *core = calloc(ncl + 1, 1);
    ll *st = malloc(sizeof(ll) * (cOff + 1)); ll sp = 0;
    ll lem = 0, nh = 0, nc = 0;
    st[sp++] = last - ncl - 1; need[last - ncl - 1] = 1; lem = 1;
    while (sp) {
        ll k = st[--sp];
        for (ll j = off[k]; j < endo[k]; j++) {
            ll h = H[j]; nh++;
            if (h > ncl) { ll q = h - ncl - 1; if (!need[q]) { need[q] = 1; lem++; st[sp++] = q; } }
            else if (!core[h]) { core[h] = 1; nc++; }
        }
    }
    printf("%lld %lld %lld\n", lem, nh, nc);
    if (argc > 3) { FILE *g = fopen(argv[3], "w"); for (ll i = 1; i <= ncl; i++) if (core[i]) fprintf(g, "%lld\n", i); fclose(g); }
    return 0;
}
