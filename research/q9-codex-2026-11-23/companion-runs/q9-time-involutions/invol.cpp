#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using A=array<int,512>;
int pop(int x){return popcount(unsigned(x));}mt19937 rng(1172317);int rn(int n){return rng()%n;}
struct DS{int par[256],bit[256];DS(int n){iota(par,par+n,0);fill(bit,bit+n,0);}int root(int i){if(par[i]==i)return i;int j=par[i];par[i]=root(j);bit[i]^=bit[j];return par[i];}bool link(int i,int j,int k){int a=root(i),b=root(j);int z=k^bit[i]^bit[j];if(a==b)return !z;par[a]=b;bit[a]=z;return 1;}};
bool good(const P&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){int w=pop(p[i]^p[j]);if((i-j==1)?w!=1:w<2)return false;}return 1;}
struct Walk{P p;int hd[512],nx[256];vector<pair<int,int>>bad;Walk(P list):p(list){fill(hd,hd+512,-1);int n=p.size();for(int i=0;i<n;i++){nx[i]=hd[p[i]];hd[p[i]]=i;for(int j=0;j<i;j++){int d=pop(p[i]^p[j]);if(i==j+1?d!=1:d<2)bad.emplace_back(i,j);}}}
 bool solve(const A& f,P &out){int n=p.size();DS ds(n);
 for(auto [i,j]:bad){int d=pop(p[i]^f[p[j]]);if(i==j+1?d!=1:d<2)return 0;if(!ds.link(i,j,1))return 0;}
 for(int i=1;i<n;i++)if(pop(f[p[i]]^p[i-1])!=1 && !ds.link(i,i-1,0))return 0;
 for(int i=0;i<n;i++){int z=f[p[i]];for(int d=-1;d<9;d++){int v=d<0?z:z^(1<<d);for(int j=hd[v];j>=0;j=nx[j])if(j<i-1&&!ds.link(i,j,0))return 0;}}
 out=p;for(int i=0;i<n;i++){ds.root(i);if(ds.bit[i])out[i]=f[p[i]];}if(!good(out))abort();return 1;}};
A iso(vector<pair<int,int>> const& pairs,int t){A f;for(int x=0;x<512;x++){int v=x;for(auto[a,b]:pairs)if(((x>>a)^(x>>b))&1)v^=1<<a|1<<b;f[x]=v^t;}for(int x=0;x<512;x++)if(f[f[x]]!=x)abort();return f;}
int main(int argc,char**argv){if(argc!=4)return 2;int mode=atoi(argv[1]),sec=atoi(argv[2]),num=atoi(argv[3]);vector<Walk> bank;string s;while(getline(cin,s)){istringstream in(s);int v;P p;while(in>>v){if(v<0||v>511)return 3;p.push_back(v);}if(p.size()>256)return 4;bank.emplace_back(p);}
 vector<A> maps;set<A> seen;auto add=[&](auto pr,int t){auto f=iso(pr,t);if(seen.insert(f).second)maps.push_back(f);};
 if(mode==0)add(vector<pair<int,int>>{{1,6}},24);
 else{for(int a=0;a<9;a++)for(int b=0;b<a;b++)for(int t=0;t<512;t++){if(((t>>a)^(t>>b))&1)continue;if(pop(t)>4||pop(t)%2)continue;add(vector<pair<int,int>>{{a,b}},t);}
 for(int i=0;i<14000;i++){array<int,9> axis; iota(axis.begin(),axis.end(),0);shuffle(axis.begin(),axis.end(),rng);int cnt=2+rn(3);vector<pair<int,int>> ps;int t=0;for(int q=0;q<cnt;q++){ps.emplace_back(axis[q*2],axis[q*2+1]);if(rn(4)==0)t^=1<<axis[q*2]|1<<axis[q*2+1];}for(int q=2*cnt;q<9;q++)if(rn(4)==0)t^=1<<axis[q];if(pop(t)%2==0)add(ps,t);}
 for(int t=1;t<512;t++)if(pop(t)==2)add(vector<pair<int,int>>{},t);}
 vector<int> order(bank.size());iota(order.begin(),order.end(),0);if(mode)shuffle(order.begin(),order.end(),rng);
 auto start=chrono::steady_clock::now();long long calls=0,solutions=0;int complete=0;P witness;
 for(int j:order){auto&w=bank[j];int offset=rn(maps.size()),step=1+rn(maps.size());while(gcd(step,int(maps.size()))!=1)step=step%maps.size()+1;
 for(int k=0;k<min(num,int(maps.size()));k++){int fi=(offset+size_t(k)*step)%maps.size();++calls;if(w.solve(maps[fi],witness)){++solutions;cout<<j<<" "<<fi;for(int x:witness)cout<<" "<<x;cout<<endl;if(mode)goto report;}}
 ++complete;if(chrono::duration<double>(chrono::steady_clock::now()-start).count()>=sec)break;}
 report:cerr<<"input "<<bank.size()<<" maps "<<maps.size()<<" completed_rows "<<complete<<" exact_systems "<<calls<<" witnesses "<<solutions<<endl;
}
