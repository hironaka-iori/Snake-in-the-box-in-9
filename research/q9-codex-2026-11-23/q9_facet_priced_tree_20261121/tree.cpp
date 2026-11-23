#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
const int IMP=-100000000;
struct Factor {
 vector<int> scope;
 vector<pair<unsigned,int>> opt;
 unordered_map<uint32_t,int> memo;
 unsigned on=0,off=0;
 int eval(unsigned a,unsigned b){
  auto key=(a<<16)|b;if(auto it=memo.find(key);it!=memo.end())return it->second;
  int best=IMP;for(auto [k,s]:opt)if((k&a)==a&&!(k&b)){best=s;break;}
  memo.emplace(key,best);return best;
 }
};
struct Search {
 vector<Factor> fac;array<vector<pair<int,unsigned>>,512> uses;
 array<int,512> val;vector<int>pool,inside;int base,scale,majority,target,cap;
 ofstream tree;long long nodes=0,boundcuts=0,empty=0,open=0,fullbad=0,found=0;int deepest=0;
 Search(string tag,string out,int threshold,int budget):target(threshold),cap(budget),tree(out){
  val.fill(-1);ifstream in(tag+".tables");assert(in);int baked,nf,nv,ni;in>>base>>scale>>baked>>nf>>nv>>ni>>majority;
  target*=scale;pool.resize(nv);inside.resize(ni);for(auto&v:pool)in>>v;for(auto&v:inside)in>>v;fac.resize(nf);
  for(int j=0;j<nf;j++){auto& f=fac[j];int arity,nopts;in>>arity>>nopts;f.scope.resize(arity);assert(arity<=16);
   for(int i=0;i<arity;i++){in>>f.scope[i];uses[f.scope[i]].push_back({j,1u<<i});}
   f.opt.resize(nopts);for(auto&[k,s]:f.opt)in>>k>>s;
  }
  assert(in&&bound()==baked);
 }
 void assign(int v,int x){
  for(auto [j,b]:uses[v]){auto&f=fac[j];f.on&=~b;f.off&=~b;if(x==1)f.on|=b;if(x==0)f.off|=b;}val[v]=x;
 }
 int bound(){
  int sum=base;
  for(auto&f:fac){int b=f.eval(f.on,f.off);if(b==IMP)return IMP;sum+=b;}return sum;
 }
 int child(int v,int x,int total){
  for(auto [j,bit]:uses[v]){auto&f=fac[j];int best=f.eval(f.on|(x?bit:0),f.off|(x?0:bit));
   if(best==IMP)return IMP;
   total+=best-f.eval(f.on,f.off);
  }
  return total;
 }
 vector<int> physical(){
  array<bool,512> chosen{};for(int v:inside)chosen[v]=true;for(int v:pool)if(val[v]==1)chosen[v]=true;
  int n=count(chosen.begin(),chosen.end(),true);if(n*scale<target)return {};
  vector<int> ends;
  for(int i=0;i<512;i++)if(chosen[i]){int deg=0;for(int d=0;d<9;d++)deg+=chosen[i^(1<<d)];
   if(deg==1)ends.push_back(i);else if(deg!=2)return {};}
  if(ends.size()!=2)return {};
  int first=popcount(unsigned(ends[0]))%2,second=popcount(unsigned(ends[1]))%2;
  if(majority==-1 ? first==second : (first!=majority||second!=majority))return {};
  vector<int> p{ends[0]};while(true){int v=p.back(),prev=p.size()>1?p[p.size()-2]:-1,next=-1;
   for(int d=0;d<9;d++){int u=v^(1<<d);if(chosen[u]&&u!=prev){next=u;break;}}
   if(next<0)break;p.push_back(next);
  }if((int)p.size()!=n)return {};
  for(int j=0;j<n;j++)for(int i=0;i<j;i++)assert(((popcount(unsigned(p[i]^p[j]))==1)==(i+1==j))&&p[i]!=p[j]);
  return p;
 }
 void visit(int b,int depth){
  deepest=max(deepest,depth);nodes++;
  if(b<target){tree<<"B "<<b<<"\n";boundcuts++;empty+=b==IMP;return;}
  if(nodes>cap){tree<<"O "<<b<<"\n";open++;return;}
  int pivot=-1,l=0,r=0;long long best=-1;int slack=b-target+1;
  for(int v:pool)if(val[v]<0){int a=child(v,0,b),c=child(v,1,b);
   int x=min(b-a,slack),y=min(b-c,slack);long long score=1LL*(x+1)*(y+1)+1LL*slack*slack*((a<target)+(c<target));
   if(score>best){best=score;pivot=v;l=a;r=c;}
   if(a<target&&c<target)break;
  }
  if(pivot<0){auto p=physical();if(p.empty()){tree<<"F "<<b<<"\n";fullbad++;}else{found++;tree<<"H "<<p.size();for(int v:p)tree<<" "<<v;tree<<"\n";}return;}
  tree<<"S "<<pivot<<"\n";assign(pivot,0);visit(l,depth+1);assign(pivot,1);visit(r,depth+1);assign(pivot,-1);
 }
};
int main(int argc,char**argv){if(argc<5)return 2;string tag=argv[1];Search search(tag,argv[2],stoi(argv[3]),stoi(argv[4]));
 if(argc>5){ifstream f(argv[5]);int v,x;while(f>>v>>x)search.assign(v,x);}
 search.visit(search.bound(),0);cout<<"nodes "<<search.nodes<<" cuts "<<search.boundcuts<<" empty "<<search.empty<<" physical_reject "<<search.fullbad<<" open "<<search.open<<" found "<<search.found<<" depth "<<search.deepest<<endl;
}
