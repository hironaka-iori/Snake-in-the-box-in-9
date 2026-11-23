// Enumerate Q6 paths close to the eight components of a Q9 reference snakepit.
// Recombine independently selected local paths in a Hamiltonian order of Q3.
#include <algorithm>
#include <array>
#include <set>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <vector>
using M=uint64_t;using P=std::vector<int>;
M B(int u){return M(1)<<u;}
int pop(M a){return __builtin_popcountll(a);}
int low(M& m){int k=__builtin_ctzll(m);m&=m-1;return k;}
struct State {M mask;int s,t,n;};
std::array<M,64> nb;
struct Family {
 M orig;int ext,min_size;
 std::vector<State> states;
 void add(int start,int end,M mask,M blocked,int extras) {
  int n=pop(mask);
  if(n>=min_size)states.push_back({mask,start,end,n});
  if(n==27 || n+pop(orig & ~blocked & ~mask)+ext-extras < min_size)return;
  M opts=nb[end] & ~blocked & ~mask;
  while(opts){
   int w=low(opts),e=extras+!(orig&B(w));
   if(e<=ext)add(start,w,mask|B(w),blocked|nb[end],e);
  }
 }
};
struct Search {
 std::array<Family,8> fam;std::array<P,8> index[64];P order,cells;
 std::array<State,8> chosen;long long nodes=0,cap,cutoffs=0;
 int target,best=0,start;bool cutoff=false;
 void cert(int depth,int total){
   P full;
   for(int i=0;i<depth;i++){
     auto s=chosen[i];M rem=s.mask;int v=s.s;
     do{full.push_back(64*order[i]+v);rem^=B(v);if(!rem)break;M x=rem&nb[v];if(pop(x)!=1)exit(6);v=__builtin_ctzll(x);}while(true);
     if(v!=s.t)exit(5);
   }
   if((int)full.size()!=total)exit(4);
   for(int j=0;j<total;j++)for(int i=0;i<j;i++)if(full[i]==full[j]||((pop(full[i]^full[j])==1)!=(i+1==j)))exit(7);
   std::cout<<"FOUND "<<total-1;for(int x:full)std::cout<<" "<<x;std::cout<<std::endl;exit(0);
 }
 bool dfs(int depth,int vertices){
  if(nodes>=cap){cutoff=true;return false;}nodes++;
  if(depth==8){best=std::max(best,vertices-1);if(vertices>=target+1)cert(depth,vertices);return false;}
  int block=order[depth];M forbidden=0,old=0;int port=0;
  for(int i=0;i<depth-1;i++)if(pop(order[i]^block)==1)forbidden|=chosen[i].mask;
  if(depth){port=chosen[depth-1].t;old=chosen[depth-1].mask^B(port);}
  M bad=forbidden|old;const auto& indices=index[port][block];
  int upper=0;for(int j=depth+1;j<8;j++)upper+=fam[order[j]].states.front().n;
  auto visit=[&](const State& s){if(vertices+s.n+upper<target+1)return -1;if(bad&s.mask)return 0;
    chosen[depth]=s;dfs(depth+1,vertices+s.n);return int(cutoff);};
  if(!depth){for(auto &s:fam[block].states)if(visit(s))break;}
  else{for(int j:indices)if(visit(fam[block].states[j]))break;}
  return false;
 }
 void arrange(int block,int used){
  order.push_back(block);
  if(order.size()==8){nodes=0;cutoff=false;dfs(0,0);total_nodes+=nodes;orders++;cutoffs+=cutoff;}
  else for(int d=0;d<3;d++){int w=block^(1<<d);if(!(used&(1<<w)))arrange(w,used|(1<<w));}
  order.pop_back();
 }
 long long total_nodes=0, orders=0;
};
int main(int argc,char**v){
 if(argc!=5 && argc!=7)return 2;
 std::array<int,8> macros{0,1,2,3,4,5,6,7};
 if(argc==7){
    std::string spec=v[6];
    if(std::string(v[5])!="perm" || spec.size()!=8)return 2;
    int used=0;
    for(int i=0;i<8;i++){
        int x=spec[i]-'0';
        if(x<0 || x>=8 || (used&(1<<x)) || (i>0 && pop(x^macros[i-1])!=1))return 2;
        macros[i]=x;used|=1<<x;
    }
 }
 int ext=atoi(v[1]),len=atoi(v[2]);Search s;s.target=atoi(v[3]);s.cap=atoll(v[4]);
 for(int u=0;u<64;u++)for(int d=0;d<6;d++)nb[u]|=B(u^(1<<d));
 for(int i=0;i<8;i++){
  auto &f=s.fam[i];f.ext=ext;f.min_size=len;std::cin>>std::hex>>f.orig;
  for(int j=0;j<64;j++){if(ext || f.orig&B(j))f.add(j,j,B(j),0,int(!(f.orig&B(j))));}
  std::sort(f.states.begin(),f.states.end(),[](const State& a,const State& b){
    if(a.n!=b.n)return a.n>b.n;if(a.s!=b.s)return a.s<b.s;return a.mask<b.mask;});
  std::cerr<<"family "<<i<<" states "<<f.states.size()<<std::endl;
  if(f.states.empty())return 0;
  for(int j=0;j<(int)f.states.size();j++)s.index[f.states[j].s][i].push_back(j);
 }
 if(argc==7){
   std::array<int,8> id{};for(int i=0;i<8;i++)id[i]=i;
   do{
    bool valid=true;for(int i=0;i<8;i++)if(__builtin_parity(i)!=__builtin_parity(id[i]))valid=false;
    if(!valid)continue;
    std::array<Family,8> old;std::array<P,8> second[64];
    // Relabel local catalogue positions to all assignments of same parity.
    for(int i=0;i<8;i++)std::swap(s.fam[id[i]],old[i]);
    for(int v=0;v<64;v++)for(int i=0;i<8;i++)std::swap(s.index[v][id[i]],second[v][i]);
    for(int i=0;i<8;i++)std::swap(s.fam[i],old[i]);
    for(int v=0;v<64;v++)for(int i=0;i<8;i++)std::swap(s.index[v][i],second[v][i]);
    s.order.assign(macros.begin(),macros.end());s.cutoff=false;s.nodes=0;s.dfs(0,0);s.total_nodes+=s.nodes;s.orders++;s.cutoffs+=s.cutoff;
    for(int i=0;i<8;i++)std::swap(s.fam[i],old[i]);
    for(int v=0;v<64;v++)for(int i=0;i<8;i++)std::swap(s.index[v][i],second[v][i]);
    for(int i=0;i<8;i++)std::swap(s.fam[id[i]],old[i]);
    for(int v=0;v<64;v++)for(int i=0;i<8;i++)std::swap(s.index[v][id[i]],second[v][i]);
   }while(std::next_permutation(id.begin(),id.end()));
 }else for(int i=0;i<8;i++)s.arrange(i,1<<i);
 std::cerr<<"orders "<<s.orders<<" visited "<<s.total_nodes<<" capped "<<s.cutoffs<<" best_complete "<<s.best<<std::endl;
 return 0;
}
