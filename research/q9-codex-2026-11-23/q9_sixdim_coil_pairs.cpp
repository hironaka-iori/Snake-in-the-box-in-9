#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>
using U=uint64_t;
U adj[64];int path_[32];
std::vector<U> cycles[8];
void list(int u,U used,int n,int largest,int L){
  for(int i=0;i<std::min(6,largest+2);i++){
    int v=u^(1<<i);U b=U(1)<<v;
    if(used&b)continue;
    bool end=n+1==L;
    U links=adj[v]&used;
    U want=U(1)<<u;
    if(end)want|=1;
    if(links!=want)continue;
    if(end){if(std::max(i,largest)==5)cycles[(L-12)/2].push_back(used|b);}
    else list(v,used|b,n+1,std::max(i,largest),L);
  }
}
U closed(U s){U a=s;while(s){int u=__builtin_ctzll(s);s&=s-1;a|=adj[u];}return a;}
bool find_cycle(int start,int u,U used,int n,U pool,int L,unsigned axes,U &result){
  U ns=adj[u]&pool&~used;
  while(ns){
    int v=__builtin_ctzll(ns);ns&=ns-1;U b=U(1)<<v;
    U want=U(1)<<u;bool end=n+1==L;
    if(end)want|=U(1)<<start;
    if((adj[v]&used)!=want)continue;
    unsigned span=axes|(v^u);
    if(end){if(span==63){result=used|b;return true;}}
    else if(find_cycle(start,v,used|b,n+1,pool,L,span,result))return true;
  }
  return false;
}
int main(int argc,char** argv){
 for(int v=0;v<64;v++)for(int i=0;i<6;i++)adj[v]|=U(1)<<(v^(1<<i));
 if(argc>1){
   list(0,1,1,-1,26);
   for(U c:cycles[7]){
    for(U p=~c;p;p&=p-1){int start=__builtin_ctzll(p);U other=0;
      if(find_cycle(start,start,U(1)<<start,1,p,26,0,other)){
        printf("disjoint26 %016llx %016llx\n",(unsigned long long)c,(unsigned long long)other);return 0;}
    }
   }
   puts("no disjoint pair of single 26-cycles");return 0;
 }
 for(int L:{12,14,16}){
   auto &bank=cycles[(L-12)/2];
   list(0,1,1,-1,L);
   sort(bank.begin(),bank.end());bank.erase(unique(bank.begin(),bank.end()),bank.end());
   for(int partner=std::max(L,28-L);partner<=32-L;partner+=2){
   long long good=0;
   for(U c:bank){
      U p=~closed(c),q=p;
      if(__builtin_popcountll(p)<partner)continue;
      while(q){
        int start=__builtin_ctzll(q);U r=0;
        if(find_cycle(start,start,U(1)<<start,1,q,partner,0,r)){
          if(good<2)printf("pair %d %016llx %016llx\n",L,(unsigned long long)c,(unsigned long long)r);
          good++;break;
        }
        q&=q-1;
      }
   }
   printf("length %d partner %d normalized %zu compatible %lld\n",L,partner,bank.size(),good);fflush(stdout);
   }
 }
}
