#include <cstdint>
#include <cstdio>
using U=uint64_t;
U adj[64],calls=0;int maximum=0;int path[64],record[64];U coil=0;int longest_coil=0;
void dfs(int v,U available,int n,int largest,U used){
 ++calls;
 if(n>maximum){maximum=n;for(int j=0;j<n;j++)record[j]=path[j];}
 // The new endpoint may close the path to the origin only if we allow that one chord.
 // Search for the closing vertex separately from valid path extensions.
 if(n>=3 && n+1>longest_coil){
   for(int i=0;i<6;i++){int w=v^(1<<i);
    if(!(used>>w&1) && (adj[w]&used)==((U(1)<<v)|1) && __builtin_popcount(w)==1)
     {coil=used|(U(1)<<w);longest_coil=n+1;break;}
   }
 }
 U next=adj[v]&available&~used;
 while(next){
  int w=__builtin_ctzll(next);next&=next-1;
  int axis=__builtin_ctz(v^w);if(axis>largest+1)continue;
  path[n]=w;dfs(w,available&~adj[v],n+1,axis>largest?axis:largest,used|(U(1)<<w));
 }
}
int main(){for(int v=0;v<64;v++)for(int i=0;i<6;i++)adj[v]|=U(1)<<(v^(1<<i));
 dfs(0,~U(0),1,-1,1);
 printf("canonical nodes %llu maximum vertices %d maximum coil vertices %d mask %016llx\n",(unsigned long long)calls,maximum,longest_coil,(unsigned long long)coil);
 for(int i=0;i<maximum;i++)printf("%d ",record[i]);puts("");
}
