#include <algorithm>
#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct S{bitset<128>sel;vector<int>v;array<int,128>d{};};array<array<unsigned char,128>,5040>perms;
int main(int argc,char**argv){
 if(argc!=4)return 2;array<int,7>pm;iota(pm.begin(),pm.end(),0);int idx=0;do{for(int x=1;x<128;x++)perms[idx][x]=perms[idx][x&(x-1)]^(1<<pm[__builtin_ctz(x)]);idx++;}while(next_permutation(pm.begin(),pm.end()));
 ifstream in(argv[1]);ofstream out(argv[2]);int limit=stoi(argv[3]),rows=0,surv=0;long long tries=0,easy=0,degree=0,forests=0;string line;
 while(rows<limit&&getline(in,line)){++rows;istringstream is(line);int id,a,b,v;is>>id>>a>>b;array<S,4> blocks;
 while(is>>v){int k=(v>>a&1)+2*(v>>b&1),z=0,n=0;for(int i=0;i<9;i++)if(i!=a&&i!=b)z|=(v>>i&1)<<n++;blocks[k].v.push_back(z);blocks[k].sel.set(z);}
 bool ok=true;for(auto &g:blocks)for(int v:g.v){for(int k=0;k<7;k++)g.d[v]+=g.sel[v^(1<<k)];if(g.d[v]>2)ok=false;}if(!ok)continue;++surv;
 for(int i=0;i<4;i++)for(int j=i+1;j<4;j++){
 auto &A=blocks[i],&B=blocks[j];array<int,512>na{},saturated{};array<array<int,9>,512>adj{};
 for(int x=0;x<512;x++)for(int k=0;k<9;k++){int u=x^(1<<k);if(u<128&&A.sel[u]){adj[x][na[x]++]=u;saturated[x]+=A.d[u]>=2;}}
 auto ordered=B.v;sort(ordered.begin(),ordered.end(),[&](int x,int y){return B.d[x]>B.d[y];});
 for(int e=0;e<9;e++)for(int f=e+1;f<9;f++){array<unsigned short,128>ext{};for(int z=0;z<128;z++){int u=0,k=0;for(int t=0;t<9;t++)if(t!=e&&t!=f)u|=(z>>k++&1)<<t;ext[z]=u;}
 int shared=((1<<e)|(1<<f))&384;vector<int>translations;for(int t=0;t<512;t++)if(!(t&shared))translations.push_back(t);
 for(int pi=0;pi<5040;pi++){
  array<int,128>img{};for(int v:ordered)img[v]=ext[perms[pi][v]];
  tries+=translations.size();
  for(int t:translations){bool legal=true;for(int v:ordered){int x=img[v]^t;if((x<128&&A.sel[x])||saturated[x]||na[x]+B.d[v]>2){legal=false;break;}}if(!legal)continue;++easy;
    array<unsigned char,128>inc{};for(int v:B.v){int x=img[v]^t;for(int z=0;z<na[x];z++){int a=adj[x][z];if(++inc[a]+A.d[a]>2){legal=false;break;}}if(!legal)break;}if(!legal)continue;++degree;
    bitset<512>set,seen;for(int v:A.v)set[v]=true;for(int v:B.v)set[img[v]^t]=true;
    for(int v=0;v<512;v++)if(set[v]&&!seen[v]){bool tip=false;vector<int>queue{v};seen.set(v);for(int q=0;q<(int)queue.size();q++){int u=queue[q],d=0;for(int k=0;k<9;k++){int y=u^(1<<k);if(set[y]){++d;if(!seen[y]){seen.set(y);queue.push_back(y);}}}tip|=d<2;}if(!tip){legal=false;break;}}
    if(legal){++forests;out<<id<<' '<<a<<' '<<b<<' '<<i<<' '<<j<<' '<<e<<' '<<f<<' '<<pi<<' '<<t<<'\n';}
   }
 }}}
 cout<<"ROW "<<id<<' '<<a<<' '<<b<<" cumulative_forests "<<forests<<endl;
 }
 cout<<"DONE rows "<<rows<<" viable_source_cuts "<<surv<<" intersecting_face_isometries "<<tries<<" passed_B_degrees "<<easy<<" both_degree_le_two "<<degree<<" acyclic_forests "<<forests<<endl;
}
