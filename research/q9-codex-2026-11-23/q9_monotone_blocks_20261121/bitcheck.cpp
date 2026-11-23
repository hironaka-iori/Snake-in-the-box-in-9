#include <algorithm>
#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
using namespace std;using Bits=bitset<512>;
struct BlockData{vector<int>v;array<int,128>d{};bitset<128>in;};
int main(int argc,char**argv){
 if(argc!=4)return 2;ifstream f(argv[1]);ofstream detail(argv[2]);int limit=stoi(argv[3]);long long cases=0,basegood=0,orient=0,trials=0,left=0;string ln;
 while(cases<limit&&getline(f,ln)){++cases;istringstream line(ln);int id,a,b,x;line>>id>>a>>b;array<BlockData,4>bs;while(line>>x){int g=(x>>a&1)+2*(x>>b&1),v=0;for(int k=8;k>=0;k--)if(k!=a&&k!=b)v=2*v+(x>>k&1);bs[g].v.push_back(v);bs[g].in[v]=1;}
 bool ok=true;for(auto &bl:bs)for(int v:bl.v){for(int k=0;k<7;k++)bl.d[v]+=bl.in[v^(1<<k)];if(bl.d[v]>2)ok=false;}if(!ok)continue;++basegood;
 for(int A=0;A<4;A++){const auto&x=bs[A];array<array<Bits,512>,3> shift{};for(int v=0;v<512;v++){
   bool legal=v>=128||!x.in[v];int n=0;for(int u:x.v)if(__builtin_popcount(u^v)==1){++n;if(x.d[u]==2)legal=false;}
   if(!legal)continue;
   for(int degree=0;degree<=2-n;degree++)for(int z=0;z<512;z++)shift[degree][z].set(v^z);
 }
 for(int B=A+1;B<4;B++){auto&y=bs[B];auto vs=y.v;stable_sort(vs.begin(),vs.end(),[&](int u,int v){return y.d[u]>y.d[v];});for(int s=0;s<9;s++)for(int t=s+1;t<9;t++){
  array<int,7>perm;int j=0;for(int k=0;k<9;k++)if(s!=k&&t!=k)perm[j++]=k;Bits allowed;int common=((1<<s)|(1<<t))&384;for(int u=0;u<512;u++)if(!(u&common))allowed.set(u);
  int ix=0;do{++orient;trials+=allowed.count();int lut[128]{};for(int u=1;u<128;u++)lut[u]=lut[u&(u-1)]|(1<<perm[__builtin_ctz(u)]);Bits tr=allowed;for(int v:vs){tr&=shift[y.d[v]][lut[v]];if(tr.none())break;}if(tr.any()){left+=tr.count();for(int j=0;j<512;j++)if(tr[j])detail<<id<<' '<<a<<' '<<b<<' '<<A<<' '<<B<<' '<<s<<' '<<t<<' '<<ix<<' '<<j<<'\n';}++ix;}while(next_permutation(perm.begin(),perm.end()));
 }}}
 }
 cout<<"DONE source_cases "<<cases<<" viable "<<basegood<<" injection_choices "<<orient<<" ambient_intersection_placements "<<trials<<" surviving_preliminary_geometry "<<left<<endl;
}
