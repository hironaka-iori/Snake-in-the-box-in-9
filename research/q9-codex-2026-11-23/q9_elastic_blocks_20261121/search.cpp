#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using V=vector<int>;
struct Variant { V offsets; bool reversed; int a,b; };
struct Block {int lo,hi; bool left; vector<Variant> variants;};
int dist(int x,int y){return popcount(unsigned(x^y));}
bool clean(const V&p){for(int i=0;i<int(p.size());++i){if(p[i]<0||p[i]>=512)return false;for(int j=0;j<i;++j)if(dist(p[i],p[j])<(i-j==1?1:2)||(i-j==1&&dist(p[i],p[j])!=1))return false;}return true;}
struct Search {
 V positions; vector<Block> blocks; array<int,512> forbid{}; mt19937 &rng; long long cap,attempts=0,accepted=0;bool truncated=false;int depth=0, extra=-1, added=-1; V witness;
 Search(const V&p,const V&cuts,mt19937&r,long long limit,int orbit):positions(p),rng(r),cap(limit){
  vector<Block> initial;
  for(size_t j=1;j<cuts.size();++j)initial.push_back({cuts[j-1],cuts[j]-1,false,{}});
  int pivot=max_element(initial.begin(),initial.end(),[](auto &a,auto &b){return a.hi-a.lo<b.hi-b.lo;})-initial.begin();
  auto root=initial[pivot];
  for(int i=root.lo;i<=root.hi;++i)mark(p[i],1);
  int l=pivot-1,h=pivot+1;
  while(l>=0||h<int(initial.size())){
   bool left=h==int(initial.size())||(l>=0&&(initial[l].hi-initial[l].lo>=initial[h].hi-initial[h].lo));
   auto b=left?initial[l--]:initial[h++];b.left=left;
   vector<pair<int,int>> axes={{0,0}};for(int a=0;a<9;++a)for(int d=a+1;d<9;++d)axes.emplace_back(a,d);
   shuffle(axes.begin()+1,axes.end(),rng);axes.resize(min<int>(orbit,axes.size()));set<V>seen;
   for(auto [a,d]:axes)for(int rev=0;rev<=1;++rev){
    V q;for(int i=0;i<=b.hi-b.lo;++i){int idx=(left!=bool(rev))?b.hi-i:b.lo+i;q.push_back(p[idx]);}
    int origin=q[0];for(auto&x:q){x^=origin;if(((x>>a)^(x>>d))&1)x^=(1<<a)|(1<<d);}
    if(seen.insert(q).second)b.variants.push_back({q,bool(rev),a,d});
   }
   shuffle(b.variants.begin(),b.variants.end(),rng);blocks.push_back(std::move(b));
  }
 }
 void mark(int v,int delta){forbid[v]+=delta;for(int d=0;d<9;++d)forbid[v^(1<<d)]+=delta;}
 bool dfs(int k){
  depth=max(depth,k);
  if(k==int(blocks.size())){witness=positions;if(extra>=0){auto &join=blocks[extra];witness.insert(witness.begin()+(join.left?join.hi+1:join.lo),added);}if(!clean(witness))abort();return true;}
  auto &b=blocks[k];int tip=positions[b.left?b.hi+1:b.lo-1];
  if(k!=extra)return attach(k,tip);
  for(int bit=0;bit<9;++bit){
   int middle=tip^(1<<bit);if(forbid[middle]!=1)continue;
   added=middle;mark(middle,1);if(attach(k,middle))return true;mark(middle,-1);
   if(truncated)return false;
  }return false;
 }
 bool attach(int k,int tip){
  auto &b=blocks[k];
  for(int d=0;d<9;++d){int anchor=tip^(1<<d);if(forbid[anchor]!=1)continue;
   for(auto &variant:b.variants){
    if(++attempts>cap){truncated=true;return false;}
    auto &v=variant.offsets;bool ok=true;
    for(size_t i=1;i<v.size();++i)if(forbid[anchor^v[i]]){ok=false;break;}
    if(!ok)continue;
    ++accepted;for(int i=0;i<int(v.size());++i){int x=anchor^v[i];mark(x,1);positions[b.left?b.hi-i:b.lo+i]=x;}
    if(dfs(k+1))return true;
    for(auto t:v)mark(t^anchor,-1);
    if(truncated)return false;
   }
  }return false;
 }
};
int main(int argc,char**argv){
 if(argc!=7)return 2;
 int trials=stoi(argv[1]),nblocks=stoi(argv[2]),seed=stoi(argv[3]),cap=stoi(argv[4]),orbit=stoi(argv[5]),control=stoi(argv[6]);mt19937 rng(seed);
 vector<V> bank;string line;while(getline(cin,line)){istringstream f(line);V p;int x;while(f>>x)p.push_back(x);if(p.size()>=3)bank.push_back(p);}
 if(bank.empty())return 3;
 long long attempts=0,accepted=0,truncated=0,good=0;int maxdepth=0;
 for(int t=0;t<trials;++t){int row=rng()%bank.size();auto p=bank[row];int n=p.size();V cuts={0,n};
  if(control==1 || control==3)cuts={0,38,77,115,153,n};
  else{while(int(cuts.size())<nblocks+1){int j=2+rng()%(n-3);bool use=true;for(int k:cuts)if(abs(j-k)<3)use=false;if(use)cuts.push_back(j);}sort(cuts.begin(),cuts.end());}
  bool valid=true;for(size_t i=1;i<cuts.size();++i)if(!clean(V(p.begin()+cuts[i-1],p.begin()+cuts[i]))){valid=false;break;}
  if(!valid)continue;
  good++; Search s(p,cuts,rng,cap,orbit);if(control==2)s.extra=rng()%s.blocks.size();
  if(control==3){for(size_t j=0;j<s.blocks.size();++j){auto &b=s.blocks[j];if((b.left?b.hi+1:b.lo)==77)s.extra=int(j);}if(s.extra<0)return 6;}
  bool found=s.dfs(0);attempts+=s.attempts;accepted+=s.accepted;truncated+=s.truncated;maxdepth=max(maxdepth,s.depth);
  if(found){cout<<"FOUND row "<<row<<" trial "<<t<<" cuts";for(int x:cuts)cout<<" "<<x;cout<<"\nPATH";for(int x:s.witness)cout<<" "<<x;cout<<endl;return 0;}
 }
 cout<<"DONE trials "<<trials<<" eligible "<<good<<" attempts "<<attempts<<" accepted "<<accepted<<" truncated "<<truncated<<" maxdepth "<<maxdepth<<endl;
}
