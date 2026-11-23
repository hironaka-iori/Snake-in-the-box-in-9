#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
using namespace std;using U=uint64_t;using P=vector<int>;
struct Tours{
 array<U,49>adj{};array<int,49>v{},walk{};int k=0;U nodes=0,count=0,limit,target;bool cut=false;int row;ofstream&out;
 Tours(const P&ms,int r,ofstream&o,U n,U t):limit(n),target(t),row(r),out(o){array<int,512>slot;slot.fill(-1);int x=0;slot[0]=0;for(int i=0;i<ms.size();i++){x^=ms[i];v[i+1]=x;slot[x]=i+1;}
 for(int odd=0;odd<512;odd++)if(popcount(unsigned(odd))%2){U s=0;for(int b=1;b<512;b*=2){int a=slot[odd^b];if(a>=0)s|=1ULL<<a;}if(popcount(s)==2){int a=countr_zero(s);U rest=s&(s-1);int b=countr_zero(rest);adj[a]|=rest;adj[b]|=1ULL<<a;}}}
 bool connected(U rem,U first){U reach=first,now=first;while(now){U next=0;for(U z=now;z;z&=z-1)next|=adj[countr_zero(z)];now=next&rem&~reach;reach|=now;}return (reach&rem)==rem;}
 void dfs(int vtx,U rem,int depth){if(cut)return;if(++nodes>limit){cut=true;return;}walk[depth]=vtx;
 if(!rem){count++;out<<row;for(int i=1;i<=depth;i++)out<<" "<<(v[walk[i]]^v[walk[i-1]]);out<<"\n";if(count>=target)cut=true;return;}
 U cand=adj[vtx]&rem;if(!cand)return;if(popcount(cand)>1){U current=rem|(1ULL<<vtx);int tips=0;for(U z=rem;z;z&=z-1){int a=countr_zero(z);U tmp=adj[a]&current;if(!tmp||(has_single_bit(tmp)&&++tips>1))return;}
 if(!connected(rem,cand&-cand))return;}
 for(;cand&&!cut;cand&=cand-1){int u=countr_zero(cand);dfs(u,rem^(1ULL<<u),depth+1);}
 }};
int main(int argc,char**argv){ifstream f(argv[1]),oi(argv[2]);ofstream out(argv[3]);int count=stoi(argv[4]);U lim=stoull(argv[5]),tgt=stoull(argv[6]);string l;vector<P>a;while(getline(f,l)){istringstream in(l);P p;int m;while(in>>m)p.push_back(m);a.push_back(p);}
 U total=0,results=0,capped=0;int id,n=0;while(n<count&&oi>>id){Tours z(a[id],id,out,lim,tgt);z.dfs(0,(1ULL<<49)-2,0);cout<<"R "<<id<<" "<<z.count<<" "<<z.nodes<<" "<<z.cut<<"\n";total+=z.nodes;results+=z.count;capped+=z.cut;n++;}
 cout<<"DONE "<<n<<" "<<total<<" "<<results<<" "<<capped<<endl;}
