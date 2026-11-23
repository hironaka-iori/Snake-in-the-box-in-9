#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
constexpr int no_option=-100000000;
void require(bool x,const char* msg){if(!x)throw runtime_error(msg);}
struct Local {
 vector<int> vertices,scores;unordered_map<uint32_t,int> cache;
 int maximum(const array<int,512>&a){
  unsigned yes=0,free=0;
  for(int i=0;i<(int)vertices.size();i++){
   int x=a[vertices[i]];if(x<0)free|=1u<<i;else if(x)yes|=1u<<i;
  }
  uint32_t code=(yes<<16)|free;if(auto it=cache.find(code);it!=cache.end())return it->second;
  int best=no_option;unsigned t=free;while(true){best=max(best,scores[yes|t]);if(!t)break;t=(t-1)&free;}
  cache.emplace(code,best);return best;
 }
};
struct Replay{
 array<int,512> assignment;array<vector<int>,512> touch;vector<int> pool,inside;
 vector<Local> factors;vector<int> values;int base,scale,col,target;ifstream proof;
 int64_t nodes=0,split=0,cuts=0,unknown=0,found=0,reject=0;int maxdepth=0;
 Replay(const string&data,const string&tree,int t):target(t),proof(tree){
  assignment.fill(-2);ifstream in(data);require(bool(in)&&bool(proof),"cannot open files");
  int root,nf,np,ni;in>>base>>scale>>root>>nf>>np>>ni>>col;target*=scale;
  pool.resize(np);for(int&v:pool){in>>v;require(assignment[v]==-2,"duplicate vertex");assignment[v]=-1;}
  inside.resize(ni);for(int&v:inside)in>>v;
  factors.resize(nf);
  for(int j=0;j<nf;j++){int n,k;in>>n>>k;auto&f=factors[j];f.vertices.resize(n);
   for(int&v:f.vertices){in>>v;touch.at(v).push_back(j);}
   f.scores.assign(1u<<n,no_option);while(k--){int mask,s;in>>mask>>s;require(f.scores.at(mask)==no_option,"duplicate mask");f.scores[mask]=s;}
   values.push_back(f.maximum(assignment));
  }
  require(bool(in)&&score()==root,"root table mismatch");
 }
 int score(){int s=base;for(int x:values){if(x==no_option)return no_option;s+=x;}return s;}
 void set(int v,int x){assignment[v]=x;for(int j:touch[v])values[j]=factors[j].maximum(assignment);}
 vector<int> physical(){
  array<int,512> selected{};for(int v:pool){require(assignment[v]>=0,"premature physical leaf");selected[v]=assignment[v];}for(int v:inside)selected[v]=1;
  int n=count(selected.begin(),selected.end(),1);if(n*scale<target)return {};
  vector<int> ends;
  for(int v=0;v<512;v++)if(selected[v]){int degree=0;for(int i=0;i<9;i++)degree+=selected[v^(1<<i)];
   if(degree==1)ends.push_back(v);else if(degree!=2)return {};}
  if(ends.size()!=2)return {};
  int first=popcount(unsigned(ends[0]))%2,second=popcount(unsigned(ends[1]))%2;
  if(col==-1 ? first==second : (first!=col||second!=col))return {};
  vector<int> p{ends.front()};
  while(true){int last=p.back();selected[last]=0;int next=-1;
   for(int i=0;i<9;i++)if(selected[last^(1<<i)]){require(next<0,"bad pair");next=last^(1<<i);}
   if(next<0)break;p.push_back(next);}
  if(int(p.size())!=n)return {};
  for(int i=0;i<n;i++)for(int j=0;j<i;j++)require((popcount(unsigned(p[i]^p[j]))==1)==(i==j+1),"witness chord");
  return p;
 }
 void go(int depth){
  char type;int datum;proof>>type>>datum;require(bool(proof),"incomplete tree");
  nodes++;maxdepth=max(maxdepth,depth);
  if(type=='S'){
   require(datum>=0&&datum<512&&assignment[datum]==-1,"invalid split");split++;
   set(datum,0);go(depth+1);set(datum,1);go(depth+1);set(datum,-1);return;
  }
  if(type=='H'){auto p=physical();require(!p.empty()&&datum==int(p.size()),"no valid witness");
   vector<int> listed(datum);for(int&v:listed)proof>>v;
   if(listed!=p)reverse(p.begin(),p.end());
   require(listed==p,"witness vertices do not match");found++;return;}
  int actual=score();require(datum==actual,"leaf bound mismatch");
  if(type=='B'){require(actual<target,"unjustified bound prune");cuts++;}
  else if(type=='O')unknown++;
  else if(type=='F'){require(physical().empty(),"discarded valid path");reject++;}
  else throw runtime_error("unknown node kind");
 }
};
int main(int argc,char**argv){
 if(argc<4||argc>5)return 2;Replay r(argv[1],argv[2],stoi(argv[3]));
 if(argc==5){ifstream p(argv[4]);require(bool(p),"cannot open pins");int v,x;while(p>>v>>x){require(v>=0&&v<512&&r.assignment[v]==-1&&(x==0||x==1),"invalid pin");r.set(v,x);}}
 r.go(0);string extra;require(!(r.proof>>extra),"extra tree records");
 cout<<"VERIFIED nodes "<<r.nodes<<" splits "<<r.split<<" bound_leaves "<<r.cuts<<" invalid_full "<<r.reject<<" open "<<r.unknown<<" witnesses "<<r.found<<" depth "<<r.maxdepth<<endl;
}
