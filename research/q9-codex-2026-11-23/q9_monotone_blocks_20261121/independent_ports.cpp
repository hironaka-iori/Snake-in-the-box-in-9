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
struct H{int need,ports,isol;};
int main(int ac,char**av){if(ac!=3)return 2;ifstream f(av[1]);ofstream log(av[2]);string ln;long long rows=0,valid=0,internalPairs=0,pass=0,halves=0,compared=0,feasible=0;
 while(getline(f,ln)){rows++;istringstream ss(ln);int id,a,b,x;ss>>id>>a>>b;array<vector<int>,4>g;array<bitset<128>,4>sets{};int dg[4][128]{};while(ss>>x){int j=(x>>a&1)+2*(x>>b&1),v=0,t=0;for(int k=0;k<9;k++)if(k!=a&&k!=b)v|=(x>>k&1)<<t++;g[j].push_back(v);sets[j].set(v);}
 bool ok=true;for(int j=0;j<4;j++)for(int v:g[j]){for(int k=0;k<7;k++)dg[j][v]+=sets[j][v^(1<<k)];if(dg[j][v]>2)ok=false;}if(!ok)continue;valid++;array<array<vector<H>,4>,4>records;
 for(int A=0;A<4;A++)for(int B=A+1;B<4;B++){
 array<array<bitset<128>,128>,2>sh{};for(int v=0;v<128;v++)for(int z=0;z<128;z++){if(!sets[A][v]||dg[A][v]<2)sh[0][z].set(v^z);if(!sets[A][v])sh[1][z].set(v^z);}
 array<int,7>p;iota(p.begin(),p.end(),0);int pi=0;do{internalPairs+=128;int lut[128]{};for(int i=1;i<128;i++)lut[i]=lut[i&(i-1)]^(1<<p[__builtin_ctz(i)]);bitset<128>tr;tr.set();
 for(int v:g[B]){tr&=sh[dg[B][v]==2][lut[v]];if(tr.none())break;}
 for(int t=0;t<128;t++)if(tr[t]){++pass;bitset<256>used,visited;for(int x:g[A])used[x]=1;for(int v:g[B])used[128+(lut[v]^t)]=1;int dsum=0,np=0,iso=0;
 for(int v=0;v<256;v++)if(used[v]){int d=0;for(int k=0;k<8;k++)d+=used[v^(1<<k)];if(d>2)abort();dsum+=2-d;np+=d<=1;iso+=d==0;}if(iso>2)continue;
 bool forest=true;for(int x=0;x<256;x++)if(used[x]&&!visited[x]){vector<int>queue{x};visited[x]=1;int edges=0;for(int i=0;i<(int)queue.size();i++){int v=queue[i];for(int k=0;k<8;k++){int u=v^1<<k;if(used[u]){edges++;if(!visited[u]){visited[u]=1;queue.push_back(u);}}}}if(edges!=2*((int)queue.size()-1))forest=false;}if(!forest)continue;
 ++halves;records[A][B].push_back({dsum,np,iso});log<<id<<' '<<a<<' '<<b<<' '<<A<<' '<<B<<' '<<pi<<' '<<t<<' '<<dsum<<' '<<np<<' '<<iso<<'\n';}
 ++pi;}while(next_permutation(p.begin(),p.end()));}
 for(int b=1;b<4;b++){int c=b==1?2:1,d=6-b-c;for(auto l:records[0][b])for(auto r:records[c][d]){compared++;int n=l.need+r.need-2;if(n%2)continue;n/=2;if(n<=0||n>min(l.ports,r.ports)||l.need-n<l.isol||r.need-n<r.isol)continue;++feasible;}}
 }
 cout<<"DONE cases "<<rows<<" viable "<<valid<<" relative_maps "<<internalPairs<<" obey_degree "<<pass<<" feasible_half_forests "<<halves<<" half_combinations "<<compared<<" compatible_connection_counts "<<feasible<<endl;
}
