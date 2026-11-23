#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
using namespace std;using Bits=bitset<512>;
array<Bits,10>wclass;array<Bits,512>hood;array<array<Bits,2>,9>half;
struct V{int t,p;};
struct Solver{
 int g,source,ctrl,lo,hi,anchor,anchorDirection,flip,off=0;array<int,9> perm,order;vector<int> original,proj,layer,chosen;
 vector<V>A,B;vector<int>sig;array<vector<Bits>,10> dom;long long nodes=0,checks=0,cores=0,rows=0,hits=0,windows=0,swindows=0,pruned=0;
 int rot(int x)const{int y=0;for(int d=0;d<9;d++)if(x>>d&1)y|=1<<perm[d];return y;}
 bool recurse(int depth,int used){
  ++nodes;if(depth==9)return true;int ax=order[depth];int avail=511^used;
  while(avail){int k=countr_zero((unsigned)avail);avail&=avail-1;auto &next=dom[depth+1];bool good=true;
   for(int i=0;i<(int)sig.size();i++){next[i]=dom[depth][i]&half[k][sig[i]>>ax&1];if(next[i].none()){good=false;break;}}
   if(good){perm[ax]=k;if(recurse(depth+1,used|(1<<k)))return true;}
  }return false;
 }
 bool solve(int l,int h){
  lo=l;hi=h;++cores;A.clear();B.clear();int n1=0;for(int i=l;i<=h;i++)n1+=layer[i];flip=n1>h-l+1-n1;
  for(int i=l;i<=h;i++)(layer[i]==flip?A:B).push_back({i,proj[i]});
  if(B.empty()){iota(perm.begin(),perm.end(),0);off=0;return true;}
  vector<int>seams;for(int i=l;i<h;i++)if(layer[i]!=layer[i+1])seams.push_back(i);
  assert(!seams.empty());
  // A seam in a dense group of other crossings constrains the relative chart.
  int seam=seams[0],score=-1;for(int s:seams){int v=0;for(int t:seams)v+=10-popcount((unsigned)(proj[s]^proj[t]));if(v>score){score=v;seam=s;}}
  anchor=proj[seam];Bits allA;array<int,512>deg{};for(auto [t,x]:A){allA[x]=1;for(int d=0;d<9;d++)deg[x^(1<<d)]++;}
  vector<Bits> allow;for(auto [t,x]:B){vector<int>ne;for(int j:{t-1,t+1})if(l<=j&&j<=h&&layer[j]==flip)ne.push_back(proj[j]);
    Bits b;for(int y=0;y<512;y++)if(!allA[y]&&deg[y]==(int)ne.size()){
       bool ok=true;for(int z:ne)if(popcount((unsigned)(y^z))!=1){ok=false;break;}if(ok)b.set(y);}
    if(b.none())return false;allow.push_back(b);
  }
  for(int d=0;d<9;d++){
    ++checks;anchorDirection=d;int tr=anchor^(1<<d);vector<pair<int,int>>ranked;vector<Bits> buckets;vector<int>s0;bool good=true;
    for(int i=0;i<(int)B.size();i++){int rel=B[i].p^anchor,k=popcount((unsigned)rel);Bits allowed;
       for(int v=0;v<512;v++)if(wclass[k][v]&&allow[i][v^tr])allowed.set(v);
       auto cnt=allowed.count();if(!cnt){good=false;break;}
       if(cnt==wclass[k].count())continue;
       int h=ranked.size();ranked.emplace_back(int(cnt),h);buckets.push_back(allowed);s0.push_back(rel);
    }
    if(!good)continue;
    sort(ranked.begin(),ranked.end());sig.clear();dom[0].clear();for(auto [c,index]:ranked){sig.push_back(s0[index]);dom[0].push_back(buckets[index]);}
    for(int i=1;i<=9;i++)dom[i].resize(sig.size());int seen=0;
    for(int j=0;j<9;j++){
      int mx=-1,idx=-1;for(int k=0;k<9;k++)if(!(seen>>k&1)){int sc=0;for(int i=0;i<(int)sig.size();i++){int re=sig[i]&~seen;if(re>>k&1)sc+=1000/(popcount((unsigned)re)*(1+ranked[i].first));}if(sc>mx){mx=sc;idx=k;}}
      order[j]=idx;seen|=1<<idx;
    }
    if(recurse(0,0)){off=tr^rot(anchor);return true;}
  }return false;
 }
 void direct(int l,int h){
  vector<int>out;for(int i=l;i<=h;i++)out.push_back(layer[i]==flip?proj[i]:off^rot(proj[i]));
  for(int j=0;j<(int)out.size();j++)for(int i=0;i<j;i++){int d=popcount((unsigned)(out[i]^out[j]));assert(j==i+1?d==1:d>1);}
  cout<<"HIT "<<source<<' '<<ctrl<<' '<<l<<' '<<h<<' '<<flip<<' '<<off<<' ';for(auto k:perm)cout<<k;cout<<' ';for(int i=0;i+1<(int)out.size();i++)cout<<countr_zero((unsigned)(out[i]^out[i+1]));cout<<endl;
 }
 void visit(int begin,int end){
   if(begin>end)return;
   if(!solve(end,begin+g)){pruned+=end-begin+1;return;}
   if(begin==end){hits++;direct(begin,begin+g);return;}
   int mid=(begin+end)/2;visit(begin,mid);visit(mid+1,end);
 }
 void run(int which, int opt,int stop){
  int n=original.size();for(ctrl=0;ctrl<10;ctrl++){if(which>=0&&ctrl!=which)continue;int b=1<<ctrl;proj.clear();layer.clear();
    for(auto x:original){proj.push_back((x&(b-1))|((x>>(ctrl+1))<<ctrl));layer.push_back((x&b)!=0);}
    int cnt=max(0,min(n-g,stop<0?n-g:stop));windows+=cnt;for(int start=0;start<cnt;start+=opt)visit(start,min(cnt-1,start+opt-1));
  }rows++;
 }
};
int main(int argc,char**argv){
 if(argc!=8)return 2;for(int x=0;x<512;x++){wclass[popcount((unsigned)x)].set(x);for(int i=0;i<9;i++)half[i][(x>>i)&1][x]=1;}
 Solver s;s.g=stoi(argv[2]);ifstream f(argv[1]);int lo=stoi(argv[3]),hi=stoi(argv[4]);string line;int id=0;
 while(getline(f,line)){if(id>=lo&&id<=hi){s.source=id;istringstream t(line);int d,x;t>>d;assert(d==10);s.original.clear();while(t>>x)s.original.push_back(x);
 s.run(stoi(argv[5]),stoi(argv[6]),stoi(argv[7]));}id++;}
 cout<<"DONE target "<<s.g<<" rows "<<s.rows<<" axis_windows "<<s.windows<<" pruned_windows "<<s.pruned<<" geometric_core_tests "<<s.cores<<" anchor_directions_tested "<<s.checks<<" permutation_dfs "<<s.nodes<<" hits "<<s.hits<<endl;
}
