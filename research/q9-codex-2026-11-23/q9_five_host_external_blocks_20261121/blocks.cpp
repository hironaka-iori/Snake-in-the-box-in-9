#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <random>
#include <vector>
using namespace std;
using Mask=bitset<512>;using P=vector<int>;
array<array<int,9>,512> nb;
struct Solver {
 int goal,cap,nodes=0;bool limited=false;P witness;
 struct Cut{
  const Mask &on;int goal,clock=0;array<int,512> tin{},low{},sub{},detach{},largest{};P visited;
  Cut(const Mask &a,int g):on(a),goal(g){}
  void dfs(int v,int par){tin[v]=low[v]=++clock;sub[v]=1;visited.push_back(v);
   for(int u:nb[v])if(on[u]&&u!=par){if(!tin[u]){dfs(u,v);sub[v]+=sub[u];low[v]=min(low[v],low[u]);
     if(low[u]>=tin[v]){detach[v]+=sub[u];largest[v]=max(largest[v],sub[u]);}}
    else low[v]=min(low[v],tin[u]);}
  }
  bool propagate(Mask &active,Mask &must,const P &verts){
   Mask large;bool found=false;
   for(int v:verts)if(active[v]&&!tin[v]){visited.clear();dfs(v,-1);int n=visited.size();if(n<goal)continue;assert(!found);found=true;
    for(int u:visited){large.set(u);if(max(largest[u],n-1-detach[u])<goal)must.set(u);}}
   if(!found||(must&~large).any())return false;active=large;return true;
  }
 };
 bool dfs(Mask active,Mask must,const P &verts){
  if(++nodes>cap){limited=true;return false;}int pivot=-1,score=-1;P neighbors;
  for(;;){
   if(active.count()<goal)return false;Cut cut(active,goal);if(!cut.propagate(active,must,verts))return false;
   Mask remove;for(int v:verts)if(active[v]){int f=0;for(int u:nb[v])f+=must[u];
    if(f>2){if(must[v])return false;remove.set(v);}
    if(f==2&&must[v])for(int u:nb[v])if(active[u]&&!must[u])remove.set(u);
   }
   if(remove.none())break;active&=~remove;
  }
  for(int v:verts)if(active[v]){P adj;int f=0;for(int u:nb[v])if(active[u]){adj.push_back(u);f+=must[u];}
   if(adj.size()>=3){int priority=8*int(adj.size())+4*int(must[v])+f;if(priority>score){pivot=v;neighbors=adj;score=priority;}}}
  if(pivot<0){
   int first=-1;bool loop=true;for(int v:verts)if(active[v]){int deg=0;for(int u:nb[v])deg+=active[u];first=v;if(deg<=1){loop=false;break;}}
   if(int(active.count())-loop<goal)return false;P w;int last=-1,x=first;
   while(w.size()<goal){w.push_back(x);int next=-1;for(int u:nb[x])if(active[u]&&u!=last){next=u;break;}last=x;x=next;}
   witness=w;return true;
  }
  if(!must[pivot]){auto reduced=active;reduced.reset(pivot);if(dfs(reduced,must,verts))return true;if(limited)return false;}
  must.set(pivot);Mask excluded;for(int u:neighbors)excluded.set(u);
  for(int j=0;j<neighbors.size();j++)for(int i=0;i<j;i++){auto drop=excluded;drop.reset(neighbors[i]);drop.reset(neighbors[j]);if((drop&must).any())continue;
   if(dfs(active&~drop,must,verts))return true;if(limited)return false;}
  return false;
 }
 bool run(const P&host,const P&outside){P all=host;all.insert(all.end(),outside.begin(),outside.end());Mask start;for(int x:all){assert(!start[x]);start.set(x);}return dfs(start,{},all);}
};
int main(int argc,char**argv){
 if(argc!=5)return 2;int mode=stoi(argv[1]),goal=stoi(argv[2])+1,cap=stoi(argv[3]),sample=stoi(argv[4]);for(int v=0;v<512;v++)for(int k=0;k<9;k++)nb[v][k]=v^(1<<k);
 string line;mt19937 rng(911377);int row=0;
 while(getline(cin,line)){P host;istringstream in(line);int v;while(in>>v)host.push_back(v);Mask h;for(int x:host)h.set(x);set<P> tested;map<int,int> hist;
  uint64_t nodes=0,unknown=0,controls=0;int proposals=0;
  auto tryone=[&](P ext){
   proposals++;sort(ext.begin(),ext.end());ext.erase(unique(ext.begin(),ext.end()),ext.end());erase_if(ext,[&](int v){return h[v];});
   if(ext.size()<4||!tested.insert(ext).second)return false;
   Solver solver{goal,cap};bool found=solver.run(host,ext);nodes+=solver.nodes;unknown+=solver.limited;hist[ext.size()]++;
   if(solver.limited||tested.size()%149==1||found){cout<<(found?"FOUND":solver.limited?"LIMIT":"AUDIT")<<" "<<row<<" "<<solver.nodes<<" outside";for(int x:ext)cout<<" "<<x;
    if(found){cout<<" vertices";for(int x:solver.witness)cout<<" "<<x;}cout<<endl;}
   return found;
  };
  if(mode==0){P ext;for(int i=0;i<sample;i++){ext.push_back(host.back());host.pop_back();}h.reset();for(int v:host)h.set(v);return tryone(ext)?0:3;}
  if(mode==1||mode==2){
   int dim=mode+2;
   for(int mask=1;mask<512;mask++)if(popcount(unsigned(mask))==dim)for(int base=0;base<512;base++)if(!(base&mask)){P xs;for(int s=mask;;s=(s-1)&mask){xs.push_back(base^s);if(!s)break;}if(tryone(xs))return 0;}
  }else{
   auto block=[&](){int base=rng()%512,mask=0;int dim=2+rng()%2;while(popcount(unsigned(mask))<dim)mask|=1<<(rng()%9);P xs;
    for(int s=mask;;s=(s-1)&mask){xs.push_back(base^s);if(!s)break;}return xs;};
   for(int t=0;t<sample;t++){P xs=block();int nblocks=2+rng()%3;for(int k=1;k<nblocks;k++){auto ys=block();xs.insert(xs.end(),ys.begin(),ys.end());}
    if(tryone(xs))return 0;}
  }
  cout<<"ROW "<<row++<<" proposals "<<proposals<<" distinct "<<tested.size()<<" UNKNOWN "<<unknown<<" nodes "<<nodes<<" sizes";for(auto [s,n]:hist)cout<<" "<<s<<"/"<<n;cout<<endl;
 }
 cout<<"DONE"<<endl;
}

