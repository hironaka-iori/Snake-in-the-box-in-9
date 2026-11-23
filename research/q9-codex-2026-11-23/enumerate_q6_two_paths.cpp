#include <cstdint>
#include <cstdio>
#include <algorithm>
using U=uint64_t;
U adj[64],bestA=0,bestB=0,checked=0,secondNodes=0;
int record=27;
void secondary(int v,U pool,U used,int n,int first,U A){
 ++secondNodes;
 if(first+n>record){record=first+n;bestA=A;bestB=used;}
 if(first+n+__builtin_popcountll(pool&~used)<=record)return;
 U next=adj[v]&pool&~used;
 while(next){int w=__builtin_ctzll(next);next&=next-1;
  secondary(w,pool&~adj[v],used|(U(1)<<w),n+1,first,A);}
}
void anchor(int v,U available,U used,int n,int largest){
 ++checked;
 // Any improving pair contains a path with more than half the current record.
 if(2*n>record){
  U pool=available&~adj[v]&~used;
  if(n+__builtin_popcountll(pool)>record){
   for(U q=pool;q;q&=q-1){
    int w=__builtin_ctzll(q);secondary(w,pool,U(1)<<w,1,n,used);
   }
  }
 }
 U next=adj[v]&available&~used;
 while(next){int w=__builtin_ctzll(next);next&=next-1;int axis=__builtin_ctz(v^w);
 if(axis<=largest+1)anchor(w,available&~adj[v],used|(U(1)<<w),n+1,std::max(largest,axis));}
}
int main(){for(int v=0;v<64;v++)for(int i=0;i<6;i++)adj[v]|=U(1)<<(v^(1<<i));
 anchor(0,~U(0),1,1,-1);
 printf("maximum vertices at most two paths %d anchor nodes %llu partner nodes %llu masks %016llx %016llx\n",record,(unsigned long long)checked,(unsigned long long)secondNodes,(unsigned long long)bestA,(unsigned long long)bestB);}
