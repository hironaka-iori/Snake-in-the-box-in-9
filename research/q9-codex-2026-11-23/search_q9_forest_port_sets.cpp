// Join independent Q8 linear forests. Every cross-edge pairs equal projections.
// Enumerate the two global endpoints first, then match the remaining port sets.
#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>
using namespace std;
using Vert=vector<int>;
using Hist=array<int,9>;
struct Forest {Vert cells,tips;bitset<256> used,single;int iso=0;};
struct Var {int f,a,b,drops;};
int target,minimum,maximum;vector<Forest> bank;
uint64_t matched=0,maps=0,joins=0,controls=0;
set<string> seen,nearSeen;
ofstream nearFile;
array<uint64_t,9> nearCount{};
int dist(int x,int y){return __builtin_popcount(unsigned(x^y));}
string canonical(const Vert&p){
 string best;for(int dir:{1,-1}){int m[9]={},n=0;string s;
 for(int i=1;i<(int)p.size();i++){int k=dir==1?i:p.size()-i;
 int b=__builtin_ctz(p[k]^p[k-1]);if(!m[b])m[b]=++n;s+=char('0'+m[b]-1);}
 if(best.empty()||s<best)best=s;}return best;
}
bool join(const Forest&A,const Forest&B,int rootX,int rootY,const array<int,8>&perm,const Vert&required){
 maps++;array<bool,512> use{};for(int x:A.cells)use[x]=true;
 for(int y:B.cells){int z=y^rootY,x=rootX;while(z){int j=__builtin_ctz(z);x^=1<<perm[j];z&=z-1;}use[x+256]=true;}
 bitset<256> cross;for(int v:required)cross.set(v);
 int extras=0;for(int v=0;v<256;v++)if(use[v]&&use[v+256]&&!cross[v])extras++;
 if(extras&&(!nearFile.is_open()||extras>8))return false;
 auto edge=[&](int x,int i){return use[x^(1<<i)]&&(i!=8||cross[x&255]);};
 int end=-1,ends=0;for(int v=0;v<512;v++)if(use[v]){int d=0;for(int i=0;i<9;i++)d+=edge(v,i);
 if(d!=2){if(d!=1||++ends>2)return false;end=v;}}
 if(ends!=2)return false;
 Vert p;int prev=-1;
 while(end>=0){p.push_back(end);int next=-1;for(int i=0;i<9;i++){int w=end^(1<<i);if(edge(end,i)&&w!=prev)next=w;}prev=end;end=next;}
 if((int)p.size()!=target+1)return false;
 if(extras){
 string key=canonical(p);if(nearSeen.insert(key).second){nearCount[extras]++;nearFile<<extras;for(int v:p)nearFile<<" "<<v;nearFile<<"\n";}
 return false;
 }
 for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||((dist(p[i],p[j])==1)!=(j==i-1)))abort();
 joins++;if(seen.insert(canonical(p)).second){cout<<"PATH";for(int v:p)cout<<" "<<v;cout<<endl;}
 return true;
}
bool aligned(const Forest&A,const Forest&B,const Vert&x,const Vert&y){
 int root=x.front();Hist ref{};for(int v:x)ref[dist(root,v)]++;
 for(int anchor:y){Hist h{};for(int v:y)h[dist(anchor,v)]++;if(h!=ref)continue;
 array<int,8> perm{};Vert lx(x.size()),ly(y.size());
 auto dfs=[&](auto&&self,int i,int used,Vert&pa,Vert&pb)->bool{
 if(i==8)return join(A,B,root,anchor,perm,x)&&target>=192;
 for(int j=0;j<8;j++)if(!(used&(1<<j))){
 int counts[256]={};Vert qa=pa,qb=pb;
 for(size_t k=0;k<x.size();k++){
 qa[k]|=(((x[k]^root)>>j)&1)<<i;
 qb[k]|=(((y[k]^anchor)>>i)&1)<<i;
 counts[qa[k]]++;counts[qb[k]]--;}
 bool ok=true;for(int z:qa)if(counts[z]){ok=false;break;}
 if(ok){perm[i]=j;if(self(self,i+1,used|(1<<j),qa,qb))return true;}
 }return false;};
 if(dfs(dfs,0,0,lx,ly))return true;
 }return false;
}
uint64_t signature(int count,int isoAndDrops,int ports,const Hist&h){
 uint64_t s=count*101+ports;s=s*7+isoAndDrops;
 for(int i=1;i<=8;i++)s=(s^uint64_t(h[i]))*1099511628211ull;return s;
}
int main(int argc,char**argv){
 if(argc<4||argc>6)return 2;if(argc>=5)nearFile.open(argv[4]);target=atoi(argv[1]);minimum=atoi(argv[2]);maximum=atoi(argv[3]);
 set<Vert> uniq;string line;int rows=0;
 while(getline(cin,line)){bool direct=line.rfind("F ",0)==0;istringstream r(direct?line.substr(2):line);Vert p;int v;
 while(r>>v){if(v<0||v>=512)abort();p.push_back(v);}if(p.empty())continue;rows++;
 for(int axis=0;axis<(direct?1:9);axis++)for(int side=0;side<(direct?1:2);side++){
 Forest f;if(direct){for(int x:p){if(x>=256)abort();f.used.set(x);}}else for(int x:p)if(((x>>axis)&1)==side)f.used.set((x&((1<<axis)-1))|((x>>(axis+1))<<axis));
 bool ok=true;for(int x=0;x<256;x++)if(f.used[x]){f.cells.push_back(x);int d=0;for(int j=0;j<8;j++)d+=f.used[x^(1<<j)];if(d>2){ok=false;break;}if(d<2)f.tips.push_back(x);if(!d){f.iso++;f.single[x]=true;}}
 if(ok&&f.iso<=2&&(int)f.tips.size()>=minimum&&(int)f.tips.size()<=maximum&&uniq.insert(f.cells).second)bank.push_back(f);
 }}
 unordered_multimap<uint64_t,Var> index;uint64_t nvars=0;
 uint64_t mutantCount=0;auto evaluate=[&](const Forest&f,int fi)->bool{int n=f.tips.size();vector<Hist> at(n,Hist{});Hist h{};
 for(int i=0;i<n;i++)for(int j=0;j<i;j++){int d=dist(f.tips[i],f.tips[j]);at[i][d]++;at[j][d]++;h[d]++;}
 auto variant=[&](int a,int b)->bool{
 int drops=(a>=0)+(b>=0);if(drops+f.iso>2)return false;Hist k=h;
 if(a>=0)for(int d=0;d<=8;d++)k[d]-=at[a][d];
 if(b>=0){for(int d=0;d<=8;d++)k[d]-=at[b][d];k[dist(f.tips[a],f.tips[b])]++;}
 auto key=signature(target+1-f.cells.size(),2-drops-f.iso,n-drops,k);
 auto [lo,hi]=index.equal_range(key);
 for(;lo!=hi;lo++){auto e=lo->second;auto &g=bank[e.f];
 if(g.cells.size()+f.cells.size()!=size_t(target+1)||e.drops+g.iso+drops+f.iso!=2||int(g.tips.size())-e.drops!=n-drops)continue;
 matched++;Vert x,y;for(int i=0;i<n;i++)if(i!=a&&i!=b)x.push_back(f.tips[i]);
 for(int i=0;i<(int)g.tips.size();i++)if(i!=e.a&&i!=e.b)y.push_back(g.tips[i]);
 if(aligned(f,g,x,y))return true;}
 if(fi>=0)index.emplace(signature(f.cells.size(),drops+f.iso,n-drops,k),Var{fi,a,b,drops});nvars++;return false;};
 if(variant(-1,-1))return true;
 for(int a=0;a<n;a++)if(!f.single[f.tips[a]]){if(variant(a,-1))return true;
 if(f.iso==0)for(int b=0;b<a;b++)if(variant(a,b))return true;}
 return false;};
 for(int fi=0;fi<(int)bank.size();fi++)if(evaluate(bank[fi],fi))return 0;
 if(argc==6){int limit=atoi(argv[5]);
 for(int fi=0;fi<min(limit,(int)bank.size());fi++){
 const auto &base=bank[fi];
 for(int v=0;v<256;v++){
 Forest f;f.used=base.used;f.used.flip(v);bool good=true;
 for(int x=0;x<256;x++)if(f.used[x]){f.cells.push_back(x);int d=0;for(int j=0;j<8;j++)d+=f.used[x^(1<<j)];
 if(d>2){good=false;break;}if(d<2)f.tips.push_back(x);if(!d){f.iso++;f.single[x]=true;if(f.iso>2){good=false;break;}}}
 if(!good||(int)f.tips.size()<minimum||(int)f.tips.size()>maximum||!uniq.insert(f.cells).second)continue;
 mutantCount++;if(evaluate(f,-1))return 0;
 }}cout<<"MUTATED "<<mutantCount<<endl;}
 if(nearFile.is_open()){cout<<"NEAR";for(int i=1;i<=8;i++)cout<<" "<<nearCount[i];cout<<endl;}
 cout<<"DONE rows "<<rows<<" forests "<<bank.size()<<" variants "<<nvars<<" hash_pairs "<<matched<<" exact_maps "<<maps<<" joins "<<joins<<" classes "<<seen.size()<<endl;
}
