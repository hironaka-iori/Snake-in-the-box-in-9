#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;using Mask=bitset<128>;
array<array<unsigned char,128>,5040>lut;vector<array<int,7>>pr;unordered_map<int,int>pid;int code(const array<int,7>&p){int t=0;for(int c:p)t=t*8+c;return t;}
struct Map{int p,t;int at(int x)const{return lut[p][x]^t;}};
Map inverse(Map x){array<int,7>rev;for(int d=0;d<7;d++)rev[pr[x.p][d]]=d;int p=pid[code(rev)];return {p,lut[p][x.t]};}
Map comp(Map f,Map g){array<int,7>v;for(int i=0;i<7;i++)v[i]=pr[f.p][pr[g.p][i]];return{pid[code(v)],f.at(g.t)};}
struct Block{Mask points,zero,one,two;vector<int>vs;};struct Edge{Map m;Mask u,v;};
struct Wedge{Map center;Mask atA,atC;int miss;};
struct Fit{
 Block b[4];vector<Edge> edge[4][4];long long mapChecks=0,pairOK=0,wedges=0,joinCandidates=0,degreesOK=0,cycles=0,internal=0,squares=0,hits=0;int id,x,y,n;
 void build(int a,int c){auto &A=b[a],&C=b[c];for(int k=0;k<5040;k++){const auto &f=lut[k];for(int t=0;t<128;t++){++mapChecks;Mask ma,mc;bool ok=true;for(int v:C.vs){int u=f[v]^t;if(!A.points[u])continue;if(A.two[u]||C.two[v]){ok=false;break;}ma.set(u);mc.set(v);}
 if(!ok||(A.zero&~ma).count()+(C.zero&~mc).count()>2)continue;
 Map m{k,t};edge[a][c].push_back({m,ma,mc});edge[c][a].push_back({inverse(m),mc,ma});++pairOK;}}}
 int deficits(int center,const Mask&l,const Mask&r){auto &B=b[center];if((B.zero&~(l|r)).any()||(B.one&l&r).any())return 3;return (B.zero&~(l&r)).count()+(B.one&~(l|r)).count();}
 bool witness(int A,int B,int C,int D,const Wedge&b1,const Wedge&d1,Map cToA){
 vector<int>vs;for(auto [id,lab,z]:{tuple{A,0,Map{0,0}},tuple{B,1,b1.center},tuple{C,3,cToA},tuple{D,2,d1.center}})for(int v:b[id].vs)vs.push_back((lab<<7)|z.at(v));
 bitset<512>sel;for(int v:vs)sel.set(v);int root=-1,tips=0;for(int v:vs){int deg=0;for(int j=0;j<9;j++)deg+=sel[v^(1<<j)];if(deg==1){root=v;tips++;}else assert(deg==2);}
 assert(tips==2);vector<int>p{root};int last=-1;while(true){int v=p.back(),nxt=-1;for(int j=0;j<9;j++){int u=v^(1<<j);if(u!=last&&sel[u]){nxt=u;break;}}if(nxt<0)break;last=v;p.push_back(nxt);}
 if((int)p.size()!=n){cycles++;return false;}for(int j=0;j<n;j++)for(int i=0;i<j;i++){int d=popcount((unsigned)(p[i]^p[j]));assert(j==i+1?d==1:d>=2);}
 cout<<"HIT "<<id<<' '<<x<<' '<<y<<' '<<A<<B<<C<<D<<' '<<b1.center.p<<' '<<b1.center.t<<' '<<cToA.p<<' '<<cToA.t<<' '<<d1.center.p<<' '<<d1.center.t;for(int v:p)cout<<' '<<v;cout<<endl;++hits;return true;
 }
 bool layout(int A,int B,int C,int D){++squares;if(edge[B][A].size()*edge[B][C].size()>edge[D][A].size()*edge[D][C].size())swap(B,D);
 unordered_map<int,vector<Wedge>>index;for(auto &l:edge[B][A])for(auto &r:edge[B][C]){
 int miss=deficits(B,l.u,r.u);if(miss>2)continue;++wedges;Map ba=inverse(l.m),ca=comp(ba,r.m);index[ca.p*128+ca.t].push_back({ba,l.v,r.v,miss});}
 if(index.empty())return false;for(auto &l:edge[D][A])for(auto &r:edge[D][C]){int miss=deficits(D,l.u,r.u);if(miss>2)continue;++wedges;Map da=inverse(l.m),ca=comp(da,r.m);auto it=index.find(ca.p*128+ca.t);if(it==index.end())continue;
 for(auto &w:it->second){++joinCandidates;int k=deficits(A,w.atA,l.v),h=deficits(C,w.atC,r.v);if(w.miss+miss+k+h!=2)continue;++degreesOK;if(witness(A,B,C,D,w,{da,l.v,r.v,miss},ca))return true;}}
 return false;}
 bool trial(const vector<int>&p){
 n=p.size();for(int i=0;i<4;i++){b[i]=Block{};for(int j=0;j<4;j++)edge[i][j].clear();}
 for(int v:p){int g=(v>>x&1)+2*(v>>y&1),u=0,k=0;for(int i=0;i<9;i++)if(i!=x&&i!=y)u|=(v>>i&1)<<k++;b[g].points.set(u);b[g].vs.push_back(u);}
 for(auto &S:b)for(int v:S.vs){int d=0;for(int j=0;j<7;j++)d+=S.points[v^(1<<j)];if(d>2){internal++;return false;}(d==0?S.zero:d==1?S.one:S.two).set(v);}
 for(int a=0;a<4;a++)for(int c=a+1;c<4;c++)build(a,c);
 for(int C=1;C<4;C++){int B=C==1?2:1,D=6-B-C;if(layout(0,B,C,D))return true;}return false;
 }
};
int main(int argc,char**argv){if(argc!=3)return 2;array<int,7>p;iota(p.begin(),p.end(),0);do{int k=pr.size();pr.push_back(p);pid[code(p)]=k;for(int v=1;v<128;v++)lut[k][v]=lut[k][v&(v-1)]^(1<<p[countr_zero((unsigned)v)]);}while(next_permutation(p.begin(),p.end()));
 ifstream f(argv[1]);Fit s;string ln;int rows=0,lim=stoi(argv[2]);while(rows<lim&&getline(f,ln)){istringstream is(ln);is>>s.id>>s.x>>s.y;vector<int>v;int a;while(is>>a)v.push_back(a);++rows;if(s.trial(v)&&v.size()>=193)break;}
 cout<<"DONE cases "<<rows<<" degree_impossible "<<s.internal<<" layouts "<<s.squares<<" relative_isometries "<<s.mapChecks<<" retained_relative "<<s.pairOK<<" wedges "<<s.wedges<<" matched_wedges "<<s.joinCandidates<<" degree_compatible "<<s.degreesOK<<" disconnected "<<s.cycles<<" hits "<<s.hits<<endl;return 0;}
