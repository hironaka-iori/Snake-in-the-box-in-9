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
array<array<Bits,2>,9>half;array<vector<int>,8>weight;
struct Ordered{
 int id,a,b;vector<int>p,z,g,y;array<vector<int>,4>S;array<bool,4>done;int target,count;long long charts=0,partial=0,placements=0,roots=0,answers=0,complete=0,rowStart=0,cap=0;bool capped=false;
 struct R{int rel;Bits dom;};
 struct Env{int block,root,pivot;vector<R>rules;array<int,7>order,perm;array<vector<Bits>,8>pool;int active;};
 bool assign(Env &e,int depth,int used,int n){
  ++partial;if(cap&&partial-rowStart>=cap){capped=true;return false;}
  if(depth==e.active){++placements;int tb=e.block;for(int i:S[tb]){int x=z[i]^e.pivot,v=e.root;for(int k=0;k<7;k++)if(x>>k&1)v^=1<<e.perm[k];y[i]=v;}
   done[tb]=true;bool ok=blocks(n+1);done[tb]=false;return ok;}
  int d=e.order[depth];for(int k=0;k<9;k++)if(!(used>>k&1)){bool ok=true;
   for(int j=0;j<(int)e.rules.size();j++){auto state=e.pool[depth][j]&half[k][e.rules[j].rel>>d&1];if(state.none()){ok=false;break;}e.pool[depth+1][j]=state;}
   if(!ok)continue;e.perm[d]=k;if(assign(e,depth+1,used|1<<k,n))return true;if(capped)return false;
  }return false;
 }
 bool blocks(int n){
  if(n==4){++complete;for(int j=0;j<count;j++)for(int i=0;i<j;i++){int h=popcount((unsigned)(y[i]^y[j]));assert(j==i+1?h==1:h>1);}++answers;cout<<"HIT "<<id<<' '<<a<<' '<<b;for(auto x:y)cout<<' '<<x;cout<<endl;return true;}
  // Choose the chart with most prescribed seams to already placed blocks.
  int tb=-1,score=-1,jp=-1,jf=-1;for(int k=0;k<4;k++)if(!done[k]){int seam=0,pt=-1,ft=-1,top=0;
   for(int t:S[k]){int nc=0,x=-1;for(int j:{t-1,t+1})if(j>=0&&j<count&&done[g[j]]){nc++;x=j;}seam+=nc;if(nc>top){top=nc;pt=t;ft=x;}}
   if(seam>score){tb=k;score=seam;jp=pt;jf=ft;}}
  if(tb<0||score<1)return false;++charts;Bits used;array<int,512>deg{};for(int t=0;t<count;t++)if(done[g[t]]){int v=y[t];assert(!used[v]);used.set(v);for(int k=0;k<9;k++)deg[v^1<<k]++;}
  vector<Bits>loc;for(int i:S[tb]){vector<int>must;for(int t:{i-1,i+1})if(t>=0&&t<count&&done[g[t]])must.push_back(y[t]);Bits allowed;
    for(int v=0;v<512;v++)if(!used[v]&&deg[v]==(int)must.size()){bool good=true;for(int q:must)if(popcount((unsigned)(q^v))!=1){good=false;break;}if(good)allowed.set(v);}
    if(allowed.none())return false;loc.push_back(allowed);}
  for(int dir=0;dir<9;dir++){Env e;e.block=tb;e.pivot=z[jp];e.root=y[jf]^1<<dir;int seen=0;bool ok=true;
    for(int j=0;j<(int)S[tb].size();j++){int x=z[S[tb][j]]^e.pivot;seen|=x;const auto &ws=weight[popcount((unsigned)x)];Bits d;for(int v:ws)if(loc[j][v^e.root])d.set(v);if(d.none()){ok=false;break;}if(d.count()!=ws.size())e.rules.push_back({x,d});}
    if(!ok)continue;sort(e.rules.begin(),e.rules.end(),[](auto &a,auto &b){return a.dom.count()<b.dom.count();});e.active=popcount((unsigned)seen);int known=0;
    for(int j=0;j<e.active;j++){int kbest=-1,top=-1;for(int k=0;k<7;k++)if((seen>>k&1)&&!(known>>k&1)){int s=0;for(auto &r:e.rules)if(r.rel>>k&1)s+=2000/((1+(int)r.dom.count())*popcount((unsigned)(r.rel&~known)));if(s>top){kbest=k;top=s;}}e.order[j]=kbest;known|=1<<kbest;}
    for(auto &t:e.pool)t.resize(e.rules.size());for(int j=0;j<(int)e.rules.size();j++)e.pool[0][j]=e.rules[j].dom;
    if(assign(e,0,0,n))return true;if(capped)return false;
  }return false;
 }
 bool run(){count=p.size();g.clear();z.clear();y.assign(count,0);for(auto &s:S)s.clear();for(int i=0;i<count;i++){int v=p[i],c=(v>>a&1)+2*(v>>b&1);g.push_back(c);S[c].push_back(i);int x=0,j=0;for(int k=0;k<9;k++)if(k!=a&&k!=b)x|=(v>>k&1)<<j++;z.push_back(x);}
 for(int c=0;c<4;c++)for(int t:S[c])for(int u:S[c])if(t<u){int h=popcount((unsigned)(z[t]^z[u]));if((u==t+1?h!=1:h<=1))return false;}
 int center=0;for(int k=1;k<4;k++)if(S[k].size()>S[center].size())center=k;done.fill(false);done[center]=true;for(int i:S[center])y[i]=p[i];++roots;return blocks(1);}
};
int main(int argc,char**argv){if(argc!=4)return 2;for(int v=0;v<512;v++){int n=popcount((unsigned)v);if(n<=7)weight[n].push_back(v);for(int k=0;k<9;k++)half[k][v>>k&1].set(v);}
 Ordered s;s.cap=stoll(argv[3]);ifstream f(argv[1]);string l;int rows=0,caps=0,limit=stoi(argv[2]);while(rows<limit&&getline(f,l)){istringstream is(l);is>>s.id>>s.a>>s.b;s.p.clear();int v;while(is>>v)s.p.push_back(v);s.rowStart=s.partial;s.capped=false;rows++;bool hit=s.run();caps+=s.capped;cout<<"ROW "<<s.id<<" result "<<(hit?"FOUND":s.capped?"LIMIT":"EXHAUSTED")<<" states "<<s.partial-s.rowStart<<endl;if(hit&&s.p.size()>=193)break;}
 cout<<"DONE rows "<<rows<<" capped "<<caps<<" roots "<<s.roots<<" chart_calls "<<s.charts<<" coordinate_states "<<s.partial<<" complete_placements "<<s.placements<<" full_solutions "<<s.complete<<" hits "<<s.answers<<endl;
}
