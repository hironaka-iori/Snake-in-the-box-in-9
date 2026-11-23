#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <iostream>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
struct SetCheck{
 array<int,512> degree{};array<char,512> fixed{},on{};Path candidates;int target;long long nodes=0;bool capped=false;
 void add(int v,int z){on[v]=z==1;for(int d=0;d<9;d++)degree[v^(1<<d)]+=z;}
 bool whole()const{
  int ends=0,root=-1;for(int v=0;v<512;v++)if(on[v]){if(degree[v]<1||degree[v]>2)return false;if(degree[v]==1){ends++;root=v;}}
  if(ends!=2)return false;
  int n=0,previous=-1;while(root>=0){n++;int next=-1;for(int d=0;d<9;d++){int x=root^(1<<d);if(on[x]&&x!=previous)next=x;}previous=root;root=next;}return n==target;
 }
 bool dfs(int i,int need){
  if(++nodes>150000){capped=true;return false;}
  if(!need)return whole();
  if((int)candidates.size()-i<need)return false;
  int v=candidates[i];bool ok=degree[v]<=2;
  for(int k=0;k<9&&ok;k++){int x=v^(1<<k);if(on[x]&&degree[x]>=2)ok=false;}
  if(ok){add(v,1);if(dfs(i+1,need-1))return true;add(v,-1);}
  if(capped)return false;return dfs(i+1,need);
 }
 bool run(const Path &keep,int n){
  target=n;for(int v:keep){fixed[v]=1;add(v,1);}for(int v:keep)if(degree[v]>2)return false;
  for(int v=0;v<512;v++)if(!fixed[v]&&degree[v]<=2){
   bool ok=true;for(int k=0;k<9;k++)if(fixed[v^(1<<k)]&&degree[v^(1<<k)]>=2){ok=false;break;}
   if(ok)candidates.push_back(v);
  }
  return dfs(0,n-keep.size());
 }
};
int main(int argc,char**argv){
 string line;int row=0;long long total=0,capped=0,nodes=0;
 while(getline(cin,line)){Path p;int v;istringstream in(line);while(in>>v)p.push_back(v);
  if(argc==2){assert(p.size()==192);Path keep;for(int i=0;i<192;i++)if(!(2<=i&&i<=6)&&!(13<=i&&i<=17))keep.push_back(p[i]);SetCheck s;assert(s.run(keep,192));cout<<"CONTROL selected vertices";for(int v=0;v<512;v++)if(s.on[v])cout<<" "<<v;cout<<endl;return 0;}
  assert(p.size()==193);
  vector<pair<int,int>> bad;for(int i=0;i<193;i++)for(int j=i+2;j<193;j++)if(popcount(unsigned(p[i]^p[j]))==1)bad.emplace_back(i,j);assert(bad.size()==1);
  set<Path> seen;long long nc=0;
  for(int end:{bad[0].first,bad[0].second})for(int c=0;c+4<193;c++){int a=max(0,end-2),b=min(192,end+2),e=c+4;if(!(e+1<a||b+1<c))continue;
   Path keep;
   for(int i=0;i<193;i++){auto ok=[&](int t){return t>=0&&t<193&&!(a<=t&&t<=b)&&!(c<=t&&t<=e);};
    if(ok(i)&&(ok(i-1)||ok(i+1)))keep.push_back(p[i]);}
   if(!seen.insert(keep).second)continue;SetCheck s;if(s.run(keep,193)){cout<<"FOUND "<<row<<" "<<a<<" "<<b<<" "<<c<<" "<<e<<endl;return 0;}
   capped+=s.capped;nc+=s.capped;nodes+=s.nodes;total++;
  }cout<<"ROW "<<row++<<" unique "<<seen.size()<<" unresolved "<<nc<<endl;
 }
 cout<<"DONE rows "<<row<<" unique "<<total<<" resolved_negative "<<total-capped<<" unresolved "<<capped<<" nodes "<<nodes<<endl;
}

