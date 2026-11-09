#include <stdio.h>
#include <stdlib.h>
static int k,V; static int in[64],deg[64],par[64];
static long long cnt=0; static double lab=0, lab1=0;
static int find(int x){while(par[x]!=x)x=par[x];return x;}
/* no path compression (need undo) - union by attaching root; store undo info */
static void rec(int v){
  if(v==V){ cnt++; double p=1,p1=1; for(int u=0;u<V;u++) if(in[u]){p*=3-deg[u]; int o=0; p1*= (deg[u]==2?1:(deg[u]==1?2:2));} lab+=p; lab1+=p1; return;}
  rec(v+1);
  /* try include v: neighbours already decided are those u<v */
  int nb[8],m=0; for(int i=0;i<k;i++){int u=v^(1<<i); if(u<v && in[u]) nb[m++]=u;}
  if(m>2) return;
  for(int j=0;j<m;j++) if(deg[nb[j]]>=2) return;
  int r[2]; for(int j=0;j<m;j++) r[j]=find(nb[j]);
  if(m==2 && r[0]==r[1]) return;
  in[v]=1; deg[v]=m; for(int j=0;j<m;j++) deg[nb[j]]++;
  par[v]=v; int old[2]; for(int j=0;j<m;j++){old[j]=r[j]; par[r[j]]=v;}
  rec(v+1);
  for(int j=0;j<m;j++) par[old[j]]=old[j];
  in[v]=0; deg[v]=0; for(int j=0;j<m;j++) deg[nb[j]]--;
}
int main(int argc,char**argv){k=atoi(argv[1]);V=1<<k;for(int i=0;i<V;i++)par[i]=i;rec(0);printf("k=%d forests=%lld labelled=%.4g\n",k,cnt,lab);}
