/* Find two vertex-disjoint induced cycles in Q6 maximizing total length (randomized DFS). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
typedef uint64_t u64;
static u64 NB[64], CN[64];
static int path[64], best1[64], bl1;
static u64 forbid_g;
static int target_min;
static long long steps;
static int found_len; static int found[64];
static int rnd(int n){ return rand()%n; }
/* DFS for induced cycle through start 0-vertex s within allowed set (not in forbid_g), length >= target */
static int dfs(int len, u64 ban, int s){
    if(++steps>3000000) return 0;
    int h=path[len-1];
    int order[6]; for(int k=0;k<6;k++) order[k]=k;
    for(int k=5;k>0;k--){int j=rnd(k+1);int t=order[k];order[k]=order[j];order[j]=t;}
    for(int q=0;q<6;q++){
        int y=h^(1<<order[q]);
        if((ban>>y&1) || (forbid_g>>y&1)) continue;
        if(NB[s]>>y&1){
            if(len+1>=target_min){ path[len]=y; found_len=len+1; for(int i=0;i<=len;i++) found[i]=path[i]; return 1; }
            continue;
        }
        path[len]=y;
        if(dfs(len+1, ban|CN[h], s)) return 1;
    }
    return 0;
}
int find_cycle(u64 forbid, int minlen, int *out){
    forbid_g=forbid; target_min=minlen;
    for(int s=0;s<64;s++){
        if(forbid>>s&1) continue;
        for(int a=0;a<6;a++){
            int x=s^(1<<a); if(forbid>>x&1) continue;
            path[0]=s; path[1]=x; steps=0;
            /* ban: s's closed nbhd except allowing closure at end: we ban CN[s] but closure test uses adjacency */
            u64 ban=(1ULL<<s)|(1ULL<<x);
            if(dfs(2, ban, s)){ for(int i=0;i<found_len;i++) out[i]=found[i]; return found_len; }
        }
    }
    return 0;
}
int verify(int *c,int L,u64 *mask){
    u64 m=0; for(int i=0;i<L;i++){ if(m>>c[i]&1) return 0; m|=1ULL<<c[i]; }
    for(int i=0;i<L;i++){ int d=__builtin_popcountll(NB[c[i]]&m); if(d!=2) return 0; }
    *mask=m; return 1;
}
int main(int argc,char**argv){
    srand(argc>1?atoi(argv[1]):1);
    for(int v=0;v<64;v++){NB[v]=0;for(int k=0;k<6;k++)NB[v]|=1ULL<<(v^(1<<k));CN[v]=NB[v]|1ULL<<v;}
    int bestT=0; int A[64],B[64],la=0,lb=0;
    time_t t0=time(0);
    while(time(0)-t0< (argc>2?atoi(argv[2]):60)){
        int c1[64]; int L1=find_cycle(0, 22+rnd(5), c1); u64 m1;
        if(!L1||!verify(c1,L1,&m1)) continue;
        int c2[64]; int L2=find_cycle(m1, 16, c2); u64 m2;
        if(!L2||!verify(c2,L2,&m2)) continue;
        /* try to extend second: search longer cycles in the remaining set */
        for(int want=L2+2; want<=40; want+=2){ int c3[64]; int L3=find_cycle(m1, want, c3); u64 m3; if(L3&&verify(c3,L3,&m3)){L2=L3; for(int i=0;i<L3;i++)c2[i]=c3[i];} else break; }
        if(L1+L2>bestT){ bestT=L1+L2; la=L1; lb=L2; for(int i=0;i<L1;i++)A[i]=c1[i]; for(int i=0;i<L2;i++)B[i]=c2[i];
            printf("{\"total\":%d,\"lenA\":%d,\"lenB\":%d,\"A\":[",bestT,la,lb); for(int i=0;i<la;i++)printf("%s%d",i?",":"",A[i]);
            printf("],\"B\":["); for(int i=0;i<lb;i++)printf("%s%d",i?",":"",B[i]); printf("]}\n"); fflush(stdout);}
    }
    return 0;
}
