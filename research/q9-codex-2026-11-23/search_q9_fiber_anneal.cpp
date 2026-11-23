// Select an arbitrary induced Q5 path at every site of a Q4 Hamiltonian path.
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
using M=uint32_t;
vector<M> opts[32][32];M nb[32];mt19937 rng;
int pick(int n){return rng()%n;}
void gen(int a,int v,M seen,M ban){
 opts[a][v].push_back(seen);
 for(M f=nb[v]&~ban;f;f&=f-1){int w=countr_zero(f);M b=1u<<w;gen(a,w,seen|b,ban|nb[v]|b);}
}
struct Chain{
 int n;vector<int> cell,port;vector<M> m;vector<vector<int>> adj;
 int conf(int i)const{int b=0;for(int j:adj[i])b+=popcount(m[i]&m[j])-(abs(i-j)==1);return b;}
 bool order(){if(cell.size()==n)return true;array<int,4>d={0,1,2,3};shuffle(d.begin(),d.end(),rng);
  for(int a:d){int y=cell.back()^(1<<a);if(find(cell.begin(),cell.end(),y)!=cell.end())continue;
   cell.push_back(y);if(order())return true;cell.pop_back();}return false;}
 void init(int k){n=k;cell={0};if(!order())abort();adj.resize(n);port.resize(n+1);m.resize(n);
  for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(popcount(unsigned(cell[i]^cell[j]))==1)adj[i].push_back(j);
  for(auto &x:port)x=pick(32);
  for(int i=0;i<n;i++){auto &o=opts[port[i]][port[i+1]];m[i]=o[pick(o.size())];}}
 void emit(int r,int len){vector<int> p;
  for(int i=0;i<n;i++){M left=m[i];int v=port[i];
   for(;;){p.push_back(32*cell[i]+v);left^=1u<<v;if(!left)break;M z=nb[v]&left;
    if(popcount(z)!=1)abort();v=countr_zero(z);}if(v!=port[i+1])abort();}
  for(int i=0;i<int(p.size());i++)for(int j=0;j<i;j++)if(p[i]==p[j]||(popcount(unsigned(p[i]^p[j]))==1)!=(j+1==i))abort();
  if(len!=p.size())abort();cout<<r<<" "<<len-1;for(int v:p)cout<<" "<<v;cout<<endl;}
 bool run(int r,int steps,int &best){
  int len=0,bad=0;for(int i=0;i<n;i++){len+=popcount(m[i]);bad+=conf(i);}bad/=2;
  for(int s=0;s<steps;s++){double frac=(s%20000)/19999.,fee=2+9*frac,temp=2-1.88*frac;
   int p=pick(n+1);bool pair=pick(3)==0&&p>0&&p<n;int i=pair?p-1:min(p,n-1),j=pair?p:i;
   int op=port[p];M a=m[i],b=m[j];
   auto score=[&](){return make_pair(popcount(m[i])+(pair?popcount(m[j]):0),conf(i)+(pair?conf(j)-popcount(m[i]&m[j])+1:0));};
   auto [l0,b0]=score();if(pair||p==0||p==n)port[p]=pick(32);
   double top=-1e12;int l1=0,b1=0;M ma=a,mb=b;
   for(int t=0;t<(pair?36:16);t++){auto &o=opts[port[i]][port[i+1]];m[i]=o[pick(o.size())];
    if(pair){auto &v=opts[port[j]][port[j+1]];m[j]=v[pick(v.size())];}
    auto [l,c]=score();double val=l-fee*c;if(val>top){top=val;l1=l;b1=c;ma=m[i];mb=m[j];}}
   double delta=l1-l0-fee*(b1-b0);
   if(delta>=0||generate_canonical<double,32>(rng)<exp(delta/temp)){m[i]=ma;m[j]=mb;len+=l1-l0;bad+=b1-b0;
    if(!bad&&len-1>best){best=len-1;emit(r,len);if(best>=192)return true;}}
   else{port[p]=op;m[i]=a;m[j]=b;}
  }return false;}
};
int main(int argc,char**argv){if(argc!=5)return 2;rng.seed(stoul(argv[1]));int n=stoi(argv[2]);if(n<1||n>16)return 2;
 for(int v=0;v<32;v++)for(int d=0;d<5;d++)nb[v]|=1u<<(v^(1<<d));
 for(int v=0;v<32;v++)gen(v,v,1u<<v,1u<<v);
 int best=-1;for(int r=0;r<stoi(argv[3]);r++){Chain c;c.init(n);if(c.run(r,stoi(argv[4]),best))break;}
 cout<<"END "<<best<<endl;}
