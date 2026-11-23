#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
using P=vector<int>;using Mask=bitset<256>;using Forest=vector<P>;
array<Mask,256> nearb;
struct Variety {Mask used,forbid;P path;};
struct Segment {P original;vector<Variety> opts;};
struct Research{
 mt19937 rng{20261120};int target,cap,extra,width;long long models=0,allopts=0,nodes=0,timeouts=0,cutoffs=0,joins=0;int maxscore=-1;set<vector<int>> classes;long long cataloghits=0; map<pair<int,int>,set<P>> pool; using Bits=vector<unsigned long long>;
 void registerPath(P v){
   int delta=v.front()^v.back();int lab[8],a=0,b=__builtin_popcount(delta);fill(lab,lab+8,-1);P code;
   for(int i=1;i<(int)v.size();i++){
    int j=__builtin_ctz(v[i]^v[i-1]);
    if(lab[j]<0)lab[j]=delta&(1<<j)?a++:b++;
    code.push_back(lab[j]);
   }
   pool[{__builtin_popcount(delta),(int)v.size()}].insert(code);
 }
 void build(const P &full){
   for(int axis=0;axis<9;axis++){
    P part;for(int i=0;i<=(int)full.size();i++){
     if(i==(int)full.size()||(i&&((full[i]^full[i-1])==(1<<axis)))){
      if(part.size()>=5&&part.size()<=48){registerPath(part);reverse(part.begin(),part.end());registerPath(part);}
      part.clear();
     }
     if(i<(int)full.size())part.push_back(((full[i]>>(axis+1))<<axis)|(full[i]&((1<<axis)-1)));
    }
   }
 }
 bool dp(Segment &s,const Mask &base,int freeFirst,int freeLast){
   P initial=s.original;
   if(freeFirst)reverse(initial.begin(),initial.end());
   // Start at a fixed portal; terminal tip can move for a terminal component.
   bool endFree=freeFirst||freeLast;int end=initial.back();
   if(initial.size()<2){s.opts.push_back({Mask(),Mask(),{}});s.opts.clear();}
   auto add=[&](P v){
     if(freeFirst)reverse(v.begin(),v.end());
     Mask u,f;for(int t:v){u.set(t);f|=nearb[t];}
     for(auto &old:s.opts)if(old.used==u)return;
     s.opts.push_back({u,f,v});
   };
   add(initial);
   if(endFree||initial.size()<5||initial.size()>48)return false;
   int delta=initial.front()^initial.back(),k=__builtin_popcount(delta);
   vector<int> yes,no;for(int d=0;d<8;d++)(delta&(1<<d)?yes:no).push_back(d);
   for(int step=0;step<8;step+=2){
    int n=initial.size()+(step==0?0:step==2?2:step==4?4:-2);
    auto it=pool.find({k,n});if(it==pool.end())continue;
    vector<const P*> donors;for(auto &c:it->second)donors.push_back(&c);
    shuffle(donors.begin(),donors.end(),rng);
    if(donors.size()>16)donors.resize(16);
    for(auto donor:donors){
     array<int,8> mapping;mapping.fill(-1);
     P path{initial.front()};
     auto expand=[&](auto &&self,int i,int used)->void{
      if(i==(int)donor->size()){cataloghits++;add(path);return;}
      int a=(*donor)[i];
      auto attempt=[&](int d,int mask){
       int x=path.back()^(1<<d);if(base[x])return;
       path.push_back(x);self(self,i+1,mask);path.pop_back();
      };
      if(mapping[a]>=0){attempt(mapping[a],used);return;}
      auto &group=a<k?yes:no;
      for(int d:group)if(!(used&(1<<d))){mapping[a]=d;attempt(d,used|(1<<d));mapping[a]=-1;}
     };
     expand(expand,0,0);if(s.opts.size()>300)break;
    }
   }return true;
 }
 void tryone(const P& full,int axis){
  Forest layers[2]; P order,which; int side=0;
  auto project=[&](int x){return ((x>>(axis+1))<<axis)|(x&((1<<axis)-1));};
  for(int i=0;i<(int)full.size();i++){
   if(i==0||((full[i]^full[i-1])==(1<<axis))){side=(full[i]>>axis)&1;order.push_back(side);which.push_back(layers[side].size());layers[side].push_back({});}
   layers[side].back().push_back(project(full[i]));
  }
  if(order.size()<5||order.size()>34)return;
  models++;int k=order.size();vector<Segment> seg(k);Mask baseOcc[2],baseForbid[2],ports;
  for(int i=0;i<k;i++){seg[i].original=layers[order[i]][which[i]];if(i)ports.set(seg[i].original.front());}
  for(int i=0;i<k;i++){
   P&v=seg[i].original;int layer=order[i];bool fixed=i==0||i==k-1||v.size()<5||v.size()>48;
   for(int j=0;j<(int)v.size();j++)if(fixed||(j==0&&i)||(j+1==(int)v.size()&&i+1<k)){
    baseOcc[layer].set(v[j]);baseForbid[layer]|=nearb[v[j]];}
  }
  for(int i=0;i<k;i++){
   P &v=seg[i].original;int layer=order[i];Mask active=baseOcc[layer];
   for(int t:v)active.reset(t);
   Mask ban;for(int t=0;t<256;t++)if(active[t])ban|=nearb[t];
   ban|=baseOcc[1-layer];if(i)ban.reset(v.front());if(i+1<k)ban.reset(v.back());
   // An endpoint shared with a neighbor must still avoid unrelated components.
   dp(seg[i],ban,i==0,i==k-1);allopts+=seg[i].opts.size();
  }
  vector<Mask> masks(k);vector<Bits> domain;vector<vector<vector<Bits>>> supports(k);
  for(int i=0;i<k;i++){
   auto &opts=seg[i].opts;stable_sort(opts.begin(),opts.end(),[](auto&a,auto&b){return a.path.size()>b.path.size();});
   auto n=opts.size();domain.emplace_back((n+63)/64,~0ULL);
   if(n%64)domain.back().back()=(1ULL<<(n%64))-1;
  }
  int rootUB=0;for(auto &s:seg)rootUB+=s.opts.front().path.size();
  if(rootUB<target+1){cutoffs++;return;}
  for(int i=0;i<k;i++){supports[i].resize(k);
   for(int j=0;j<k;j++)if(i!=j){
    auto &g=supports[i][j];g.resize(seg[i].opts.size());
    for(int ai=0;ai<(int)seg[i].opts.size();ai++){
     auto &a=seg[i].opts[ai];auto &m=g[ai];m.assign(domain[j].size(),0);
     for(int bj=0;bj<(int)seg[j].opts.size();bj++){
      auto &b=seg[j].opts[bj];bool ok=order[i]==order[j]?(a.used&b.forbid).none():(a.used&b.used&~ports).none();
      if(ok)m[bj/64]|=1ULL<<(bj%64);joins++;
     }
    }
   }
  }
  auto first=[](const Bits& v){for(int i=0;i<(int)v.size();i++)if(v[i])return i*64+__builtin_ctzll(v[i]);return -1;};
  auto count=[](const Bits&v){int n=0;for(auto m:v)n+=__builtin_popcountll(m);return n;};
  int np=0;
  auto dfs=[&](auto&&self,vector<Bits> d)->bool{
   if(++np>cap)return false;
   for(;;){
    vector<int> opt(k);int ub=0;
    for(int i=0;i<k;i++){int x=first(d[i]);if(x<0)return false;ub+=(opt[i]=seg[i].opts[x].path.size());}
    if(ub<target+1)return false;
    bool change=false;
    for(int i=0;i<k;i++) for(int word=0;word<(int)d[i].size();word++){
     auto m=d[i][word];
     while(m){
      int bit=__builtin_ctzll(m),ai=word*64+bit;m&=m-1;int upper=seg[i].opts[ai].path.size();
      for(int j=0;j<k;j++)if(i!=j){
       auto &g=supports[i][j][ai];
       int best=-1;for(int t=0;t<(int)g.size();t++){auto z=g[t]&d[j][t];if(z){best=__builtin_ctzll(z)+64*t;break;}}
       if(best<0){upper=-1;break;}
       upper+=seg[j].opts[best].path.size();
      }
      if(upper<target+1){d[i][word]&=~(1ULL<<bit);change=true;}
     }
    }
    if(!change)break;
   }
   int id=-1,small=1<<29;for(int i=0;i<k;i++){int n=count(d[i]);if(n>1&&n<small){small=n;id=i;}}
   if(id==-1){
    P w;for(int i=0;i<k;i++)for(int v:seg[i].opts[first(d[i])].path)w.push_back(v+256*order[i]);
    for(int a=0;a<(int)w.size();a++)for(int b=0;b<a;b++)assert(w[a]!=w[b]&&((__builtin_popcount(w[a]^w[b])==1)==(a==b+1)));
    assert((int)w.size()>=target+1);cout<<"FOUND "<<w.size()-1;for(int v:w)cout<<" "<<v;cout<<endl;return true;
   }
   for(int t=0;t<(int)d[id].size();t++){auto m=d[id][t];while(m){
    int bit=__builtin_ctzll(m),ai=t*64+bit;m&=m-1;
    auto next=d;fill(next[id].begin(),next[id].end(),0);next[id][t]=1ULL<<bit;
    for(int j=0;j<k;j++)if(id!=j){
     auto &g=supports[id][j][ai];for(int w=0;w<(int)next[j].size();w++)next[j][w]&=g[w];
    }
    if(self(self,next))return true;if(np>=cap)return false;
   }}
   return false;
  };if(dfs(dfs,domain))exit(0);nodes+=np;if(np>=cap)timeouts++;

 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;Research s;s.target=stoi(argv[1]);s.cap=stoi(argv[2]);s.extra=stoi(argv[3]);s.width=stoi(argv[4]);
 for(int t=0;t<256;t++){nearb[t].set(t);for(int i=0;i<8;i++)nearb[t].set(t^(1<<i));}
 string line;vector<P> bank;while(getline(cin,line)){istringstream in(line);int x;P p;while(in>>x)p.push_back(x);s.build(p);bank.push_back(p);}int rows=0;for(auto &p:bank){
 for(int a=0;a<9;a++)s.tryone(p,a);rows++;
 if(rows%50==0)cerr<<"progress "<<rows<<" "<<s.models<<" "<<s.timeouts<<" placements "<<s.cataloghits<<endl;}
 long long items=0;for(auto &pair:s.pool)items+=pair.second.size();
 cerr<<"sources "<<rows<<" donor classes "<<items<<" models "<<s.models<<" placements "<<s.cataloghits<<" opts "<<s.allopts<<" rootcuts "<<s.cutoffs<<" nodes "<<s.nodes<<" capped "<<s.timeouts<<" joins "<<s.joins<<endl;
}
