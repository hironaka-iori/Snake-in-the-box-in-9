#include <cstdio>
#include <cstdint>
int main(){
 int candidates=0,regular=0,bestspan=0;
 for(unsigned ds=1;ds<65536;ds++){
  if((ds&279u)!=278u || __builtin_popcount(ds)!=9)continue; // bits 1,2,4,8 are present; 0 absent
  unsigned nb[16]={};
  for(int u=0;u<16;u++)for(int d=1;d<16;d++)if(ds>>d&1)nb[u]|=1u<<(u^d);
  for(unsigned S=1;S<65536;S+=2){
   if(__builtin_popcount(S)!=7)continue;
   candidates++;bool ok=true;unsigned seen=0;
   for(unsigned a=S;a;a&=a-1){int u=__builtin_ctz(a);if(__builtin_popcount(nb[u]&S)!=2){ok=false;break;}}
   if(!ok)continue;regular++;
   for(unsigned todo=S;todo;){
    int start=__builtin_ctz(todo),u=start,prev=-1;unsigned dirs=0;
    do {todo&=~(1u<<u); unsigned next=nb[u]&S;if(prev>=0)next&=~(1u<<prev);
        int v=__builtin_ctz(next);dirs|=1u<<(v^u);prev=u;u=v;}while(u!=start);
    int span=__builtin_popcount(dirs);if(!seen||span<(int)seen)seen=span;
   }
   if((int)seen>bestspan){bestspan=seen;printf("new %d D %u S %u\n",bestspan,ds,S);}
  }
 }
 printf("tested %d regular %d bestspan %d\n",candidates,regular,bestspan);
}
