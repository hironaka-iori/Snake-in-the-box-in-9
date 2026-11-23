#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
using Mask=bitset<512>;
array<Mask,512> closed;
struct Arm {Path p;Mask used,halo;};
struct Stats{uint64_t cases=0,nodes=0,capped=0,arms=0,nonempty=0,both=0,joins=0,filter=0;};
vector<pair<int,int>> defects(const Path&p){
 vector<pair<int,int>> result;
 for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));assert(d>0&&p[i]>=0&&p[i]<512);if(i==j+1)assert(d==1);else if(d==1)result.push_back({j,i});}
 return result;
}
#ifdef TIP_SEARCH
#include "tip_extension.inc"
#endif
struct Enumerate{
 const Path &p;int root,dir,endlen,s,g,cost,cap;mt19937 &rng;
 array<int,512> occupied{},touch{};array<array<int,9>,2> map{};array<int,2> taken{};Path arm;
 array<array<int,9>,202> options{};int nodes=0;bool limited=false;vector<Arm> bank;
 Enumerate(const Path &p_,int l,int r,bool left,int size1,int gap,int budget,int capacity,mt19937 &gen):
 p(p_),root(left?l:r),dir(left?-1:1),endlen(left?l:p.size()-1-r),s(size1),g(gap),cost(budget),cap(capacity),rng(gen){
  for(int t=l;t<=r;t++)mark(p[t],1);
  for(int i=0;i<endlen;i++){iota(options[i].begin(),options[i].end(),0);shuffle(options[i].begin(),options[i].end(),rng);
   int d=countr_zero(unsigned(p[root+dir*i]^p[root+dir*(i+1)]));if(rng()%2)iter_swap(options[i].begin(),find(options[i].begin(),options[i].end(),d));}
 }
 void mark(int v,int n){occupied[v]+=n;for(int d=0;d<9;d++)touch[v^(1<<d)]+=n;}
 void search(int h,int x){
  if(limited)return;if(++nodes>cost){limited=true;return;}
  if(h==endlen){Arm z;z.p=arm;for(int v:arm){z.used.set(v);z.halo|=closed[v];}bank.push_back(z);if((int)bank.size()>=cap)limited=true;return;}
  bool gap=h>=s&&h<s+g;int phase=h>=s+g,original=countr_zero(unsigned(p[root+dir*h]^p[root+dir*(h+1)]));int &mapped=map[phase][original];
  for(int f:options[h]){int bit=1<<f;bool newdim=false;
   if(!gap){if(mapped&&mapped!=bit)continue;if(!mapped){if(taken[phase]&bit)continue;newdim=true;}}
   int y=x^bit;if(occupied[y]||touch[y]!=1)continue;
   if(newdim){mapped=bit;taken[phase]|=bit;}mark(y,1);arm.push_back(y);search(h+1,y);arm.pop_back();mark(y,-1);
   if(newdim){mapped=0;taken[phase]^=bit;}if(limited)return;
  }
 }
};
bool run(const Path&p,int l,int r,int s1,int g1,int s2,int g2,const vector<pair<int,int>>&bad,int budget,int cap,mt19937&rng,Stats&st,bool control=false){
 st.cases++;for(auto [a,b]:bad)if((a>=l&&b<=r)||(a>=l-s1&&b<=l)||(a>=r&&b<=r+s2)||b<=l-s1-g1||a>=r+s2+g2){st.filter++;return false;}
 array<vector<Arm>,2> banks;
 for(bool left:{true,false}){Enumerate e(p,l,r,left,left?s1:s2,left?g1:g2,budget,cap,rng);e.search(0,p[left?l:r]);st.nodes+=e.nodes;st.capped+=e.limited;st.arms+=e.bank.size();
  if(e.bank.empty())return false;st.nonempty++;banks[!left]=move(e.bank);}
 st.both++;
 for(auto &a:banks[0])for(auto &b:banks[1]){st.joins++;if((a.halo&b.used).any())continue;
  Path out(a.p.rbegin(),a.p.rend());out.insert(out.end(),p.begin()+l,p.begin()+r+1);out.insert(out.end(),b.p.begin(),b.p.end());assert(out.size()==p.size()&&defects(out).empty());
#ifdef TIP_SEARCH
  compatible++;if(bodies.insert(key(out)).second&&Extend(out).search(false))return true;continue;
#endif
  cout<<(control?"CONTROL":"FOUND")<<" l "<<l<<" r "<<r<<" gaps "<<s1<<" "<<g1<<" "<<s2<<" "<<g2<<" vertices";for(int v:out)cout<<" "<<v;cout<<endl;return true;}
 return false;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;int jobs=stoi(argv[1]),budget=stoi(argv[2]),cap=stoi(argv[3]);mt19937 rng(stoul(argv[4]));
 for(int v=0;v<512;v++){closed[v].set(v);for(int k=0;k<9;k++)closed[v].set(v^(1<<k));}
 vector<Path> bank;vector<vector<pair<int,int>>>bad;string s;int claimed;
 while(cin>>claimed>>s){if(claimed!=2)continue;Path p{0};for(char c:s){assert(c>='0'&&c<='8');p.push_back(p.back()^(1<<(c-'0')));}
  auto b=defects(p);assert(b.size()==2);
#ifdef TIP_SEARCH
  assert(p.size()==193);p=Path(p.begin()+3,p.end()-3);b=defects(p);
#endif
  bank.push_back(p);bad.push_back(b);}
 Stats st;
 if(!jobs){assert(bank.size()==1);bool ok=run(bank[0],9,bank[0].size()-10,3,2,3,2,bad[0],budget,cap,rng,st,true);return ok?0:4;}
 assert(bank.size()==34);
 for(int t=0;t<jobs;t++){
  int row=rng()%bank.size();auto &p=bank[row];assert(p.size()==193||p.size()==187);
  int l=7+rng()%65,r=p.size()-1-(7+rng()%65);
  auto shape=[&](int len){int g=1+rng()%min(12,len-2),s=1+rng()%(len-g-1);return pair{s,g};};
  auto [s1,g1]=shape(l);auto [s2,g2]=shape(p.size()-1-r);
  if(run(p,l,r,s1,g1,s2,g2,bad[row],budget,cap,rng,st)){cout<<"source "<<row<<endl;return 0;}
 }
#ifdef TIP_SEARCH
 cout<<"TIPS compatible_joins "<<compatible<<" unique_bodies "<<bodies.size()<<" extension_nodes "<<extensionnodes<<" best "<<maxedge<<" classes191 "<<w191.size()<<endl;
#endif
 cout<<"DONE trials "<<st.cases<<" initial_filters "<<st.filter<<" nodes "<<st.nodes<<" capped_side_searches "<<st.capped<<" saved_arms "<<st.arms<<" nonempty_side_searches "<<st.nonempty<<" both_sides "<<st.both<<" joins "<<st.joins<<endl;
 return 0;
}
