#include <algorithm>
#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_map>
#include <vector>
using namespace std;using Bits=bitset<256>;
struct Forest{int pi,tx;vector<int>v;array<signed char,256>d;};
struct Part{int id,a,b;array<vector<int>,4>g;array<array<vector<Forest>,4>,4>h;};
int main(int ac,char**av){if(ac!=4)return 2;ifstream f(av[1]),sigs(av[2]);ofstream out(av[3]);vector<array<int,7>>pr;array<int,7>p;iota(p.begin(),p.end(),0);do{pr.push_back(p);}while(next_permutation(p.begin(),p.end()));unordered_map<int,Part>parts;string ln;while(getline(f,ln)){istringstream l(ln);int id,a,b,x;l>>id>>a>>b;auto&v=parts[id*100+a*10+b];v.id=id;v.a=a;v.b=b;while(l>>x){int g=((x>>a)&1)+2*((x>>b)&1),z=0,k=0;for(int j=0;j<9;j++)if(j!=a&&j!=b)z|=(x>>j&1)<<k++;v.g[g].push_back(z);}}
 int id,a,b,A,B,pi,t,dem,pt,iso;while(sigs>>id>>a>>b>>A>>B>>pi>>t>>dem>>pt>>iso){auto &r=parts.at(id*100+a*10+b);Forest h{pi,t,r.g[A]};h.d.fill(-1);for(int x:r.g[B]){int v=t;for(int i=0;i<7;i++)if(x>>i&1)v^=1<<pr[pi][i];h.v.push_back(v+128);}for(int v:h.v)h.d[v]=0;for(int v:h.v)for(int k=0;k<8;k++)h.d[v]+=h.d[v^1<<k]>=0;r.h[A][B].push_back(move(h));}
 long long count=0,emb=0,deg=0,forest=0;int minparts=1000;for(auto&[k,r]:parts)for(int b=1;b<4;b++){int c=b==1?2:1,d=6-b-c;for(auto&l:r.h[0][b])for(auto&s:r.h[c][d]){
 ++count;array<array<Bits,256>,2>allowed{};for(int v=0;v<256;v++)for(int z=0;z<256;z++){if(l.d[v]<2)allowed[0][z].set(v^z);if(l.d[v]<0)allowed[1][z].set(v^z);}
 auto coords=s.v;sort(coords.begin(),coords.end(),[&](int x,int y){return s.d[x]>s.d[y];});array<int,8>pr;iota(pr.begin(),pr.end(),0);int jj=0;
 do{emb+=256;int M[256]{};for(int x=1;x<256;x++)M[x]=M[x&(x-1)]^(1<<pr[__builtin_ctz(x)]);Bits poss;for(int tx=0;tx<256;tx++){bool good=true;for(int x:s.v){int dl=l.d[M[x]^tx];if(dl>=0&&(dl==2||s.d[x]==2)){good=false;break;}}if(good)poss.set(tx);}if(poss.any()){deg+=poss.count();for(int t=0;t<256;t++)if(poss[t]){bitset<512>used,seen;for(int x:l.v)used.set(x);for(int x:s.v)used.set(256+(M[x]^t));bool ok=true;int comps=0;
 for(int x=0;x<512;x++)if(used[x]&&!seen[x]){comps++;vector<int>q{x};seen[x]=1;int before=0;for(int i=0;i<(int)q.size();i++)for(int j=0;j<9;j++){int v=q[i]^1<<j;if(used[v]){before++;if(!seen[v]){seen.set(v);q.push_back(v);}}}if(before!=2*((int)q.size()-1)){ok=false;break;}}
 if(ok){forest++;minparts=min(minparts,comps);out<<r.id<<' '<<r.a<<' '<<r.b<<" 0"<<b<<c<<d<<' '<<l.pi<<' '<<l.tx<<' '<<s.pi<<' '<<s.tx<<' '<<jj<<' '<<t<<' '<<comps<<' '<<used.to_string()<<'\n';}}}
 jj++;}while(next_permutation(pr.begin(),pr.end()));
 }}
 cout<<"DONE complementary_forests "<<count<<" interhalf_relative_isometries "<<emb<<" maximum_degree_two "<<deg<<" acyclic_forests "<<forest<<" minimum_components "<<(forest?minparts:-1)<<endl;
}
