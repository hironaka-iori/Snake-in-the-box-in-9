// Search for an induced path by moving both tails through independent cube isometries.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Mask=array<uint64_t,8>;
struct Copy{Mask points{},boundary{};array<int,9> image{};};
bool intersects(const Mask&a,const Mask&b){for(int i=0;i<8;i++)if(a[i]&b[i])return true;return false;}
void insert(Mask&m,int v){m[v/64]|=1ULL<<(v%64);}
bool valid(const vector<int>&p){for(size_t i=0;i<p.size();i++)for(size_t j=0;j<i;j++)if(p[i]==p[j]||((popcount((unsigned)(p[i]^p[j]))==1)!=(j+1==i)))return false;return true;}
int moved(int x,const array<int,9>&m){int y=0;while(x){y|=m[countr_zero((unsigned)x)];x&=x-1;}return y;}
struct Tail{
 int anchor,depths=0;array<char,512>bad{};array<int,512>mapped{};array<int,9>order{},prior{},im{},preferred{};array<vector<int>,9>ready;vector<int>rel;vector<Copy>opts;
 long long nodes=0;int cap; bool limited=false;
 Tail(const vector<int>&p,int l,int r,bool left,int limit):anchor(p[left?l:r]),cap(limit){
  for(int i=l;i<=r;i++){int x=p[i]^anchor;bad[x]=1;if(x)for(int d=0;d<9;d++)bad[x^1<<d]=1;}
  for(int i=left?0:r+1;i<(left?l:(int)p.size());i++)rel.push_back(p[i]^anchor);
  int seen=0,all=0;for(int x:rel)all|=x;
  while(seen!=all){int best=-1,score=-1;for(int d=0;d<9;d++)if((all&~seen)&1<<d){int n=0;
    for(int x:rel)n+=(x&~(seen|1<<d))==0;if(n>score){best=d;score=n;}}
   prior[depths]=seen;order[depths]=best;seen|=1<<best;
   for(int x:rel)if((x&1<<best)&&!(x&~seen))ready[depths].push_back(x);
   depths++;
  }
 }
 void visit(int h,int available){
  nodes++;if(h==depths){if((int)opts.size()>=cap){limited=true;return;}
   Copy z;z.image=im;for(int x:rel){int v=anchor^mapped[x];insert(z.points,v);insert(z.boundary,v);for(int d=0;d<9;d++)insert(z.boundary,v^(1<<d));}opts.push_back(z);return;
  }
  int bit=1<<order[h],before=prior[h];
  for(int f=available;f&&!limited;f&=f-1){
   int y=f&-f;im[order[h]]=y;
   for(int t=before;;t=(t-1)&before){mapped[t|bit]=mapped[t]|y;if(t==0)break;}
   bool ok=true;for(int x:ready[h])if(bad[mapped[x]]){ok=false;break;}
   if(ok)visit(h+1,available^y);
  }
 }
};
int main(int argc,char**argv){
 if(argc!=6)return 2;int seed=atoi(argv[1]),trials=atoi(argv[2]),minpart=atoi(argv[3]),cap=atoi(argv[4]),batch=atoi(argv[5]);mt19937 rng(seed);
 vector<vector<int>> paths;vector<vector<pair<int,int>>> defects;string line;long long nodes=0,joins=0,complete=0,limited=0,filtered=0,attempted=0,pairs=0;
 while(getline(cin,line)){istringstream s(line);int x;vector<int>p;while(s>>x){if(x<0||x>=512)abort();p.push_back(x);}if(p.empty())continue;
  vector<pair<int,int>> bad;for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){if(p[i]==p[j]||(i==j+1&&popcount((unsigned)(p[i]^p[j]))!=1))abort();if(j+1<i&&popcount((unsigned)(p[i]^p[j]))==1)bad.push_back({j,i});}
  paths.push_back(p);defects.push_back(bad);
 }
 for(int it=0;it<trials;it++){int k=rng()%paths.size();auto p=paths[k];int n=p.size()-1;
  int lo=minpart+rng()%(n-3*minpart+1),hi=lo+minpart+rng()%(n-2*minpart-lo+1);
  if(rng()%2){int a=n-hi;hi=n-lo;lo=a;}
  auto internal=[&](int a,int b){for(auto [i,j]:defects[k])if(a<=i&&j<=b)return true;return false;};
  if(internal(0,lo)||internal(lo,hi)||internal(hi,n)){filtered++;continue;}
  attempted++;Tail left(p,lo,hi,true,cap),right(p,lo,hi,false,cap);
  auto*l=&left,*r=&right;if(lo<n-hi)swap(l,r);
  l->visit(0,511);if(!l->opts.empty())r->visit(0,511);nodes+=l->nodes+r->nodes;
  if(l->limited||r->limited)limited++;else complete++;
  if(!l->opts.empty()&&!r->opts.empty())pairs++;
  for(auto &a:left.opts)for(auto &b:right.opts){joins++; if(intersects(a.boundary,b.points))continue;
   for(int i=0;i<lo;i++)p[i]=p[lo]^moved(p[i]^p[lo],a.image);for(int i=hi+1;i<=n;i++)p[i]=p[hi]^moved(p[i]^p[hi],b.image);
   if(!valid(p))abort();cout<<"FOUND "<<n<<" "<<lo<<" "<<hi<<" vertices";for(int x:p)cout<<" "<<x;cout<<endl;return 0;
  }
  if(attempted%batch==0)cout<<"progress "<<it<<" eligible "<<attempted<<" complete "<<complete<<" capped "<<limited<<" candidates_both "<<pairs<<" joins "<<joins<<" nodes "<<nodes<<endl;
 }
 cout<<"DONE eligible "<<attempted<<" complete "<<complete<<" capped "<<limited<<" filtered "<<filtered<<" candidates_both "<<pairs<<" joins "<<joins<<" nodes "<<nodes<<endl;
}
