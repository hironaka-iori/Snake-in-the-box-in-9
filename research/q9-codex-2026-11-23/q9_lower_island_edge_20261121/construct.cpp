#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
using P=vector<int>;
int dist(int a,int b){return popcount((unsigned)(a^b));}
struct Trie{array<int,8> next{};};
struct Search{
 vector<Trie> trie{1}; int map[8],blocked[256],occ[256]{},adj[256]{},id=0,best2=0,best3=0,cap,minseed,freecap;
 long long nodes=0,native=0,queries=0,saturated=0,tailcuts=0,tailnodes=0,placements=0,joins=0,local=0,budget=0,skipped=0;
 P low,seed,link,tail,ans2,ans3;int y,z,s,e; bool hit=false;mt19937 rng{151025};array<int,8> order; ofstream out;
 void add(string w){array<int,8> m;m.fill(-1);int next=0,node=0;for(char c:w){int k=c-'0';if(m[k]<0)m[k]=next++;int d=m[k];if(!trie[node].next[d]){trie[node].next[d]=trie.size();trie.push_back({});}node=trie[node].next[d];}}
 void mark(int v,int d){occ[v]+=d;for(int k=0;k<8;k++)adj[v^(1<<k)]+=d;}
 bool can(int v){return !blocked[v]&&!occ[v]&&adj[v]==1;}
 void save(const P& bridge,const P& arm){
    int n=1+low.size()+bridge.size()+arm.size();int& best=arm.empty()?best2:best3;
    if(n<=best)return;
    P v{z,y};for(auto i=bridge.rbegin();i!=bridge.rend();++i)v.push_back(256+*i);
    v.insert(v.end(),low.begin(),low.end());for(int a:arm)v.push_back(256+a);
    if(int(v.size())!=n+1)abort();
    for(int i=0;i<=n;i++)for(int j=0;j<i;j++)if(v[i]==v[j]||(dist(v[i],v[j])==1)!=(i==j+1))abort();
    best=n;if(arm.empty())ans2=v;else ans3=v;if(n>=192)hit=true;
 }
 // Complete a free upper tail after the bridge has been selected.
 void grow(const P& bridge){
    if(hit||budget>=freecap)return;
    ++budget;++tailnodes;save(bridge,tail);
    int u=tail.back();
    for(auto k:order){int v=u^(1<<k);if(!can(v))continue;tail.push_back(v);mark(v,1);grow(bridge);mark(v,-1);tail.pop_back();if(budget>=freecap||hit)break;}
 }
 void joined(){
    ++joins;save(seed,{});if(occ[e]||adj[e])return;
    mark(e,1);tail={e};budget=0;grow(seed);tailcuts+=budget>=freecap;mark(e,-1);tail.clear();
 }
 // An unconstrained short piece can complete a long catalogue prefix, including on the bridge.
 void finish(int u,int room){
    if(hit||local>=800)return;
    ++local;++native;
    if(dist(u,y)==1){if(adj[y]==1&&!occ[y]){mark(y,1);seed.push_back(y);joined();seed.pop_back();mark(y,-1);}return;}
    if(dist(u,y)>room||room<2)return;
    for(int k:order){int v=u^1<<k;if(!can(v))continue;mark(v,1);seed.push_back(v);finish(v,room-1);seed.pop_back();mark(v,-1);if(hit||local>=800)break;}
 }
 void placements_at(int node,int u,int taken){
    if(hit||nodes>=cap)return;
    ++nodes;++placements;int n=seed.size();
    if(dist(u,y)==1&&adj[y]==1){mark(y,1);seed.push_back(y);joined();seed.pop_back();mark(y,-1);return;}
    if(n>=minseed && (n%5==0||n>=90) && dist(u,y)<=5){local=0;++queries;finish(u,dist(u,y)+4);saturated+=local>=800;}
    for(int k=0;k<8;k++){int child=trie[node].next[k];if(!child)continue;
      auto accept=[&](int d,int used){int v=u^1<<d;if(!can(v))return;mark(v,1);seed.push_back(v);placements_at(child,v,used);seed.pop_back();mark(v,-1);};
      if(map[k]>=0)accept(map[k],taken);else for(int d:order)if(!(taken>>d&1)){map[k]=d;accept(d,taken|1<<d);map[k]=-1;if(hit||nodes>=cap)break;}
      if(hit||nodes>=cap)break;
    }
 }
 void run(P p,int a,int b){
    best2=best3=0;ans2.clear();ans3.clear();
    for(int i=0;i<2;i++){if(i)reverse(p.begin(),p.end());low=p;s=p.front();e=p.back();
      for(int j=0;j<2;j++){y=j?b:a;z=j?a:b;fill(blocked,blocked+256,0);for(int v:p)blocked[v]=1;blocked[a]=blocked[b]=1;
        fill(map,map+8,-1);iota(order.begin(),order.end(),0);shuffle(order.begin(),order.end(),rng);nodes=0;mark(s,1);seed={s};
        placements_at(0,s,0);mark(s,-1);skipped+=nodes>=cap;
        if(hit)break;
      }
      if(hit)break;
    }
    for(auto v:{ans2,ans3})if(!v.empty()){out<<id<<' '<<v.size()-1;for(int x:v)out<<' '<<x;out<<endl;}
 }
};
int main(int argc,char**argv){if(argc!=9)return 2;Search z;z.cap=stoi(argv[4]);z.minseed=stoi(argv[5]);z.freecap=stoi(argv[6]);z.out.open(argv[3]);ifstream bank(argv[1]);string w;while(bank>>w){z.add(w);reverse(w.begin(),w.end());z.add(w);}
 ifstream in(argv[2]);int a,b,limit=stoi(argv[7]),stride=stoi(argv[8]),count=0;
 for(int i=0;in>>w>>a>>b;i++){
  if(i>=limit&&i%stride)continue;P p{0};for(auto c:w)p.push_back(p.back()^1<<(c-'0'));z.id=i;z.run(p,a,b);++count;if(z.hit)break;
 }
 cout<<"cases "<<count<<" trie "<<z.trie.size()<<" prefix_nodes "<<z.placements<<" capped_orientations "<<z.skipped<<" free_bridge_calls "<<z.queries<<" bridge_nodes "<<z.native<<" capped_bridge_calls "<<z.saturated<<" finished_bridges "<<z.joins<<" free_tail_nodes "<<z.tailnodes<<" capped_tails "<<z.tailcuts<<" found192 "<<z.hit<<endl;
}
