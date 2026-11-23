#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;
using U=uint64_t;using P=array<int,14>;
U adj[64];set<U> six;set<pair<U,U>> seven;
struct Layout{U a,b;};
bool has(Layout m,int v){return ((v<64?m.a:m.b)>>(v%64))&1;}
vector<P> paths(Layout m,int dim){
 vector<P> result;
 for(int v=0;v<(1<<dim);v++)if(has(m,v)){
  vector<int> nb;for(int j=0;j<dim;j++)if(has(m,v^(1<<j)))nb.push_back(v^(1<<j));
  if(nb.size()!=1)continue;
  P p;p[0]=v;p[1]=nb[0];
  for(int i=2;i<14;i++){int next=-1;for(int j=0;j<dim;j++){
   int w=p[i-1]^(1<<j);if(w!=p[i-2]&&has(m,w))next=w;}
   if(next<0)abort();p[i]=next;
  }result.push_back(p);
 }return result;
}
pair<U,U> canonical(Layout m,int dim){
 pair<U,U> best={~U(0),~U(0)};
 for(auto p:paths(m,dim)){
  vector<int> order,left;
  for(int i=1;i<14;i++){int d=__builtin_ctz(p[i]^p[i-1]);if(find(order.begin(),order.end(),d)==order.end())order.push_back(d);}
  for(int d=0;d<dim;d++)if(find(order.begin(),order.end(),d)==order.end())left.push_back(d);
  do{
   vector<int> axes=order;axes.insert(axes.end(),left.begin(),left.end());
   U a=0,b=0;for(int v=0;v<(1<<dim);v++)if(has(m,v)){
    int y=0;for(int j=0;j<dim;j++)y|=(((v^p[0])>>axes[j])&1)<<j;
    (y<64?a:b)|=U(1)<<(y%64);
   }best=min(best,make_pair(a,b));
  }while(next_permutation(left.begin(),left.end()));
 }return best;
}
void mate(int u,U used,U pool,int n,U first){
 if(n==14){six.insert(canonical({first|used,0},6).first);return;}
 for(U q=adj[u]&pool&~used;q;q&=q-1){int w=__builtin_ctzll(q);mate(w,used|(U(1)<<w),pool&~adj[u],n+1,first);}
}
void first(int u,U used,U pool,int n,int mx){
 if(n==14){
  U rest=pool&~adj[u]&~used;
  if(__builtin_popcountll(rest)>=14)for(U q=rest;q;q&=q-1){int w=__builtin_ctzll(q);mate(w,U(1)<<w,rest,1,used);}return;
 }
 for(U q=adj[u]&pool&~used;q;q&=q-1){int w=__builtin_ctzll(q),d=__builtin_ctz(w^u);
  if(d<=mx+1)first(w,used|(U(1)<<w),pool&~adj[u],n+1,max(mx,d));}
}
int main(){
 for(int v=0;v<64;v++)for(int d=0;d<6;d++)adj[v]|=U(1)<<(v^(1<<d));
 first(0,1,~U(0),1,-1);
 fprintf(stderr,"six types %zu\n",six.size());
 for(U source:six){
  set<U> imgs;array<int,6> pm={0,1,2,3,4,5};
  do{
   int mapping[64]={};for(int v=1;v<64;v++)mapping[v]=mapping[v&(v-1)]|(1<<pm[__builtin_ctz(v)]);
   for(int t=0;t<64;t++){U m=0;for(U q=source;q;q&=q-1)m|=U(1)<<(mapping[__builtin_ctzll(q)]^t);imgs.insert(m);}
  }while(next_permutation(pm.begin(),pm.end()));
  for(U a:six)for(U b:imgs)if(!(a&b))seven.insert(canonical({a,b},7));
 }
 fprintf(stderr,"seven types %zu\n",seven.size());
 for(auto [a,b]:seven)printf("%016llx %016llx\n",(unsigned long long)a,(unsigned long long)b);
}
