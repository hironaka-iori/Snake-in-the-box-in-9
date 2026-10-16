/* Experimental cost probe only. This is not a proof certificate. */
#define main original_main
#include "snake_dfs.c"
#undef main

typedef struct { bs region; uint64_t hash; unsigned short head, need; } entry;
#define TABLE_BITS 21
static entry *table;
static long long hits, expanded;
static int use_block=0;
typedef struct { uint64_t rows[40],hash; unsigned short n,need; } iso_entry;
static iso_entry *iso_table;
static long long iso_hits;
static iso_entry *canonical_state(int head,bs r,uint64_t *rows,int *n,uint64_t *hash) {
    bs_set(&r,head);
    int count=0;for(int i=0;i<8;i++)count+=__builtin_popcountll(r.w[i]);
    if(count>40)return NULL;
    int deg[512]={0},pos[512],q[40],a=0,b=1;
    uint64_t color[512]={0};
    for(int v=0;v<512;v++)if(bs_has(&r,v))for(int k=0;k<9;k++)deg[v]+=bs_has(&r,v^(1<<k));
    for(int v=0;v<512;v++)if(bs_has(&r,v)) {
        color[v]=(uint64_t)deg[v]<<40;
        for(int k=0;k<9;k++){int w=v^(1<<k);if(bs_has(&r,w))color[v]+=1ULL<<(4*deg[w]);}
    }
    for(int i=0;i<512;i++)pos[i]=-1;
    q[0]=head;pos[head]=0;
    while(a<b) {
        int v=q[a++],next[9],nn=0;
        for(int k=0;k<9;k++){int w=v^(1<<k);if(bs_has(&r,w)&&pos[w]<0)next[nn++]=w;}
        for(int i=0;i<nn;i++)for(int j=i+1;j<nn;j++)
            if(color[next[j]]<color[next[i]]||(color[next[j]]==color[next[i]]&&next[j]<next[i])){
                int t=next[i];next[i]=next[j];next[j]=t;
            }
        for(int i=0;i<nn;i++){pos[next[i]]=b;q[b++]=next[i];}
    }
    *n=b;*hash=1469598103934665603ULL^b;
    for(int i=0;i<b;i++) {
        rows[i]=0;
        for(int k=0;k<9;k++){int w=q[i]^(1<<k);if(pos[w]>=0)rows[i]|=1ULL<<pos[w];}
        *hash^=rows[i];*hash*=1099511628211ULL;*hash^=*hash>>29;
    }
    return &iso_table[*hash&((1<<18)-1)];
}
static int disc[512],low[512],tick,eu[2304],ev[2304],etop,nb;
static bs blocks[512];
static void block_dfs(int v,int parent,const bs *region) {
    disc[v]=low[v]=++tick;
    for(int k=0;k<9;k++) {
        int w=v^(1<<k);
        if(!bs_has(region,w)||w==parent) continue;
        if(!disc[w]) {
            eu[etop]=v;ev[etop++]=w;
            block_dfs(w,v,region);
            if(low[w]<low[v]) low[v]=low[w];
            if(low[w]>=disc[v]) {
                bs_clear(&blocks[nb]);
                int a,b;
                do { --etop;a=eu[etop];b=ev[etop];bs_set(&blocks[nb],a);bs_set(&blocks[nb],b); } while(a!=v||b!=w);
                nb++;
            }
        } else if(disc[w]<disc[v]) {
            eu[etop]=v;ev[etop++]=w;
            if(disc[w]<low[v])low[v]=disc[w];
        }
    }
}
static int block_dp(int v,int parent) {
    int best=0;
    for(int b=0;b<nb;b++) if(b!=parent&&bs_has(&blocks[b],v)) {
        int size=0,tail=0;
        for(int word=0;word<8;word++) {
            uint64_t bits=blocks[b].w[word];
            while(bits) {
                int x=64*word+__builtin_ctzll(bits);bits&=bits-1;size++;
                if(x!=v) { int t=block_dp(x,b);if(t>tail)tail=t; }
            }
        }
        if(size-1+tail>best)best=size-1+tail;
    }
    return best;
}
static int block_bound(int h,bs r) {
    bs_set(&r,h);memset(disc,0,sizeof disc);tick=etop=nb=0;
    block_dfs(h,-1,&r);return block_dp(h,-1);
}

static bs reachable(int head, const bs *ban) {
    bs seen; bs_clear(&seen);
    int q[MAXV], a=0, b=0;
    for (int k=0;k<9;k++) {
        int x=head^(1<<k);
        if (!bs_has(ban,x)) { bs_set(&seen,x); q[b++]=x; }
    }
    while(a<b) {
        int v=q[a++];
        for(int k=0;k<9;k++) {
            int x=v^(1<<k);
            if(!bs_has(ban,x)&&!bs_has(&seen,x)) { bs_set(&seen,x); q[b++]=x; }
        }
    }
    return seen;
}
static int memo_search(int head, bs ban, int need) {
    if (++nodes>node_limit) { aborted=1; return 0; }
    if (!need) return 0;
    bs r=reachable(head,&ban);
    uint64_t h=1469598103934665603ULL ^ head;
    for(int i=0;i<8;i++) { h^=r.w[i]; h*=1099511628211ULL; h^=h>>29; }
    entry *e=&table[h&((1<<TABLE_BITS)-1)];
    if(e->need && e->hash==h && e->head==head && !memcmp(&e->region,&r,sizeof r) && e->need<=need) {
        hits++; return e->need - 1;
    }
    expanded++;
    int ub=region_bound(head,&ban,&allowed_g,NULL,-1);
    if(use_block&&ub>=need) { int bb=block_bound(head,r);if(bb<ub)ub=bb; }
    uint64_t rows[40],ih=0;int in=0;iso_entry *ie=NULL;
    if(iso_table&&ub>=need) {
        ie=canonical_state(head,r,rows,&in,&ih);
        if(ie&&ie->need&&ie->hash==ih&&ie->n==in&&ie->need<=need&&!memcmp(ie->rows,rows,in*sizeof(uint64_t))) {
            iso_hits++;return ie->need-1;
        }
    }
    if(ub>=need) {
        int best=0;
        bs next=ban; bs_or(&next,&CN[head]);
        for(int k=0;k<9;k++) {
            int x=head^(1<<k);
            if(!bs_has(&ban,x)) {
                int b=1+memo_search(x,next,need-1);
                if(b>=need) return b;
                if(b>best) best=b;
            }
            if(aborted) return 0;
        }
        ub=best;
    }
    e->region=r; e->hash=h; e->head=head; e->need=ub+1;
    if(ie){memcpy(ie->rows,rows,in*sizeof(uint64_t));ie->hash=ih;ie->n=in;ie->need=ub+1;}
    return ub;
}
int main(int argc,char **argv) {
    int keep=argc>1?atoi(argv[1]):144;
    node_limit=argc>2?atoll(argv[2]):100000000;
    use_block=argc>3?atoi(argv[3]):0;
    if(argc>4&&atoi(argv[4]))iso_table=calloc(1<<18,sizeof(iso_entry));
    table=calloc(1<<TABLE_BITS,sizeof(entry));
    if(!table) return 5;
    init_cube(9); for(int v=0;v<512;v++) bs_set(&allowed_g,v);
    int n,p[512],idx=0;
    while(scanf("%d",&n)==1) {
        if(n<keep||n>512||keep<2) return 3;
        for(int i=0;i<n;i++) if(scanf("%d",&p[i])!=1) return 3;
        if(!verify_path(p,n)) return 4;
        bs ban; bs_clear(&ban);
        for(int i=0;i<keep-1;i++) bs_or(&ban,&CN[p[i]]);
        nodes=hits=expanded=aborted=iso_hits=0;
        int ub=memo_search(p[keep-1],ban,193-keep);
        printf("{\"index\":%d,\"keep\":%d,\"nodes\":%lld,\"hits\":%lld,\"iso_hits\":%lld,\"expanded\":%lld,\"status\":\"%s\"}\n",idx++,keep,nodes,hits,iso_hits,expanded,aborted?"UNKNOWN":ub>=193-keep?"FOUND":"INFEASIBLE");
        fflush(stdout);
    }
    free(table);
}
