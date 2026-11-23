#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
struct Pair{array<vector<int>,2>arm;int edges()const{return arm[0].size()+arm[1].size();}};
uint32_t seed;uint32_t rnd(){seed^=seed<<13;seed^=seed>>17;seed^=seed<<5;return seed;}
uint64_t nodes=0,calls=0,finished=0,changed=0;
vector<int> path,picked;array<int,256>deny;array<bool,256>endok;int dest,remain,best,ceiling,threshold,ties;bool terminal;
void verify(const Pair&s){const auto&a=s.arm[0],&b=s.arm[1];assert(a.front()==b.front());vector<int>p(a.rbegin(),a.rend());for(auto x:b)p.push_back(x+256);p.push_back(b.back());
 for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)assert(p[i]!=p[j]&&((popcount(unsigned(p[i]^p[j]))==1)==(j+1==i)));}
void save(const Pair&s,int run,int it){verify(s);cout<<"BEST "<<s.edges()<<" "<<run<<" "<<it<<" "<<s.arm[0].size()<<" "<<s.arm[1].size();for(auto&a:s.arm)for(auto v:a)cout<<" "<<v;cout<<endl;}
array<int,256> price,endPrice;int unit;
int defects(const Pair&s){bool in[256]{};for(int v:s.arm[0])in[v]=1;int cost=-1;for(int y:s.arm[1])cost+=in[y];int x=s.arm[1].back();cost+=2*in[x];for(int d=0;d<8;d++)cost+=in[x^(1<<d)];return cost;}
void nearout(const Pair&s,int run,int time){cout<<"NEAR "<<s.edges()<<" "<<defects(s)<<" "<<run<<" "<<time<<" "<<s.arm[0].size()<<" "<<s.arm[1].size();for(auto&a:s.arm)for(int x:a)cout<<" "<<x;cout<<endl;}
void dfs(int v,int cost){
 if(remain--<=0)return;nodes++;int n=path.size();
 if(terminal||v==dest){if(n>=threshold){finished++;int score=12*n-unit*(cost+(terminal?endPrice[v]:0));if(score>best)best=score,ties=0;if(score==best&&rnd()%++ties==0)picked=path;}if(!terminal)return;}
 if(n>=ceiling)return;if(!terminal&&n+popcount(unsigned(v^dest))>ceiling)return;
 int ns[8],hits=0;for(int d=0;d<8;d++){int y=v^(1<<d);if(!deny[y])ns[hits++]=y;}
 deny[v]++;for(int d=0;d<8;d++)deny[v^(1<<d)]++;
 for(int j=hits-1;j>=0&&remain>0;j--){int r=rnd()%(j+1),y=ns[r];swap(ns[r],ns[j]);
  if(!terminal&&y!=dest&&deny[dest])continue;path.push_back(y);dfs(y,cost+price[y]);path.pop_back();}
 deny[v]--;for(int d=0;d<8;d++)deny[v^(1<<d)]--;
}
bool mutation(Pair&s,int budget,int upperCap){
 int side=rnd()&1;auto &a=s.arm[side],&b=s.arm[1-side];int n=a.size();
 if(n<4)return false;
 int mode=rnd()%100;int hi,lo;if(mode<33){hi=n-1;lo=max(0,hi-1-int(rnd()%35));}
 else {lo=rnd()%(n-2);int width=mode<68?2+rnd()%6:6+rnd()%25;hi=min(n-1,lo+width);}
 int costBefore=defects(s);
 if(costBefore&&rnd()%100<68){vector<int>hot;bool mask[256]{};for(int v:b)mask[v]=1;
   for(int j=1;j<n;j++){int v=a[j];if(mask[v]||(side==0&&popcount(unsigned(v^b.back()))<=1))hot.push_back(j);}
   if(side){int v=a.back();for(int u:b)if(popcount(unsigned(u^v))<=1){hot.push_back(n-1);break;}}
   if(!hot.empty()){int h=hot[rnd()%hot.size()];lo=max(0,h-1-int(rnd()%11));hi=min(n-1,h+1+int(rnd()%11));}
 }
 terminal=hi==n-1;dest=terminal?-1:a[hi];int cap=side?upperCap:96;
 ceiling=min(cap-(n-hi+lo-1),hi-lo+1+int(2+rnd()%9));
 threshold=max(2,hi-lo+1-(rnd()%16==0?2:0));
 endok.fill(true);deny.fill(0);
 price.fill(0);endPrice.fill(0);for(int j=1;j<b.size();j++)price[b[j]]++;
 if(side==0){int x=b.back();price[x]+=2;for(int d=0;d<8;d++)price[x^(1<<d)]++;}
 else for(int v:b){endPrice[v]+=2;for(int d=0;d<8;d++)endPrice[v^(1<<d)]++;}
 for(int j=0;j<n;j++)if(j<lo||j>hi){int x=a[j];deny[x]++;for(int d=0;d<8;d++)deny[x^(1<<d)]++;}
 deny[a[lo]]=0;if(dest>=0)deny[dest]=0;
 path={a[lo]};best=-100000;ties=0;picked.clear();remain=budget;calls++;dfs(a[lo],price[a[lo]]);
 if(picked.empty())return false;vector<int>z(a.begin(),a.begin()+lo);z.insert(z.end(),picked.begin(),picked.end());z.insert(z.end(),a.begin()+hi+1,a.end());
 if(z==a)return false;a=move(z);changed++;return true;
}
int main(int argc,char**argv){assert(argc==6);ifstream f(argv[1]);int n,m;vector<Pair>pool;while(f>>n>>m){Pair p;p.arm[0].resize(n);p.arm[1].resize(m);for(auto&a:p.arm)for(int&x:a)f>>x;verify(p);pool.push_back(p);}
 seed=stoul(argv[2]);int runs=stoi(argv[3]),steps=stoi(argv[4]),upperCap=stoi(argv[5]),global=0;Pair champion;
 for(auto&s:pool)if(s.edges()>global){champion=s;global=s.edges();}save(champion,-1,-1);
 int mincost=999;
 for(int run=0;run<runs;run++){int id=rnd()%pool.size();for(int k=0;k<6;k++){int v=rnd()%pool.size();if(pool[v].edges()>pool[id].edges())id=v;}
 Pair state=pool[id],elite=state;int rank=1000,local=0;float slope=0.8+float(rnd()%330)/100,baseT=0.35+float(rnd()%140)/100;
 for(int t=0;t<steps;t++){Pair next=state;unit=int(12*slope)+(rnd()%17)-8;if(unit<2)unit=2;
  if(rnd()%67==0){int s=rnd()%2,d=rnd()%8,e=(d+1+rnd()%7)%8;for(auto&v:next.arm[s])if(((v>>d)^(v>>e))&1)v^=(1<<d)|(1<<e);}
  else if(!mutation(next,350+rnd()%1850,upperCap))continue;
  int dc=defects(next),n=next.edges();if(!dc){local=max(local,n);if(n>pool[id].edges())pool[id]=next;if(n>global){global=n;save(next,run,t);if(n>=192)return 0;}}
  if(n>=192&&dc<mincost){mincost=dc;nearout(next,run,t);}
  auto energy=[&](const Pair&z){return (192-z.edges())+slope*defects(z);};
  float gain=energy(state)-energy(next),temp=baseT*(0.18+1-float(t%200)/200);if(gain>=0||((rnd()+0.5)/4294967296.0<exp(gain/temp)))state=next;
  int val=3*max(0,192-n)+4*dc;if(val<rank||(val==rank&&rnd()%9==0)){elite=next;rank=val;}
  if(t%200==199&&rnd()%4){state=elite;}
 }
 if(run%100==99)cout<<"AT "<<run+1<<" best "<<global<<" near "<<mincost<<" nodes "<<nodes<<" calls "<<calls<<" changed "<<changed<<endl;
 }cout<<"DONE "<<runs<<" "<<global<<" "<<mincost<<" "<<nodes<<" "<<calls<<" "<<finished<<" "<<changed<<endl;}
