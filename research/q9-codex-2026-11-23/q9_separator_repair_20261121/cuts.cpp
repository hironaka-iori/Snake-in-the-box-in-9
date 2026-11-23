#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
using V=vector<int>;
struct H{
 V pts;array<int,512>slot;vector<V> adj;V leaves,branch;int edges=0;bool old=false;
 H(V p):pts(p),adj(p.size()){
  slot.fill(-1);for(int i=0;i<pts.size();i++)slot[pts[i]]=i;
  for(int v=0;v<512;v++){V nb;for(int d=0;d<9;d++){int a=slot[v^(1<<d)];if(a>=0)nb.push_back(a);}
   if(nb.size()!=2)continue;int x=nb[0],y=nb[1];if(find(adj[x].begin(),adj[x].end(),y)!=adj[x].end())continue;
   adj[x].push_back(y);adj[y].push_back(x);edges++;}
  int excess=0;V forced(pts.size());for(int i=0;i<pts.size();i++){if(adj[i].size()==1)leaves.push_back(i);if(adj[i].size()>=3)branch.push_back(i);if(adj[i].size()<=2)for(int a:adj[i])forced[a]++;}
  for(int f:forced)excess+=max(0,f-2);
  old=edges>=int(pts.size())-1&&leaves.size()<=2&&excess<=2&&none_of(adj.begin(),adj.end(),[](auto&a){return a.empty();});
 }
 struct Result{int components,endpoint_need,delta;};
 Result assess(V cut){
  int n=pts.size();V tag(n,-1);for(int v:cut)tag[v]=-2;int comps=0,need=0;
  for(int a:leaves)if(tag[a]==-2)need++;
  for(int start=0;start<n;start++)if(tag[start]==-1){V q{start};tag[start]=comps;int tips=0;set<int>boundary;
   for(int i=0;i<q.size();i++){int x=q[i];tips+=(adj[x].size()==1);for(int y:adj[x]){if(tag[y]==-2){boundary.insert(y);continue;}if(tag[y]==-1){tag[y]=comps;q.push_back(y);}}}
   need+=max(tips,2-min(2,int(boundary.size())));comps++;
  }
  return {comps,need,max(comps-int(cut.size())-1,need-2)};
 }
};
int main(){string w;int row=0,distinct=0,oldok=0,certs=0;set<V> seen;
 while(cin>>w){V p{0};for(auto c:w)p.push_back(p.back()^(1<<(c-'0')));V a;for(int i=0;i<p.size();i+=2)a.push_back(p[i]);sort(a.begin(),a.end());if(a.size()!=97||adjacent_find(a.begin(),a.end())!=a.end())return 2;
  if(!seen.insert(a).second){row++;continue;}distinct++;H h(a);auto cc=h.assess({}).components;
  if(cc!=1||!h.old){row++;continue;}oldok++;int best=0;V top;H::Result observed{};
  for(int x:h.branch){V cut{x};auto f=h.assess(cut);if(f.delta>0&&10*f.delta+2>best){best=10*f.delta+2;top=cut;observed=f;}}
  for(int i=0;i<h.branch.size();i++)for(int j=0;j<i;j++){V cut{h.branch[i],h.branch[j]};auto f=h.assess(cut);if(f.delta>0&&10*f.delta+1>best){best=10*f.delta+1;top=cut;observed=f;}}
  if(best){cout<<"C "<<row<<" "<<h.edges<<" "<<h.leaves.size()<<" "<<observed.components<<" "<<observed.endpoint_need<<" "<<top.size();for(int x:top)cout<<" "<<a[x];cout<<"\n";certs++;}
  row++;
 }
 cerr<<"ROWS "<<row<<" distinct "<<distinct<<" pass_original_filters "<<oldok<<" separators "<<certs<<endl;
}
