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
void dfs(int v){
 if(remain--<=0)return;nodes++;int n=path.size();
 if((terminal&&endok[v])||v==dest){if(n>=threshold){finished++;if(n>best)best=n,ties=0;if(n==best&&rnd()%++ties==0)picked=path;}if(!terminal)return;}
 if(n>=ceiling)return;if(!terminal&&n+popcount(unsigned(v^dest))>ceiling)return;
 int ns[8],hits=0;for(int d=0;d<8;d++){int y=v^(1<<d);if(!deny[y])ns[hits++]=y;}
 deny[v]++;for(int d=0;d<8;d++)deny[v^(1<<d)]++;
 for(int j=hits-1;j>=0&&remain>0;j--){int r=rnd()%(j+1),y=ns[r];swap(ns[r],ns[j]);
  if(!terminal&&y!=dest&&deny[dest])continue;path.push_back(y);dfs(y);path.pop_back();}
 deny[v]--;for(int d=0;d<8;d++)deny[v^(1<<d)]--;
}
bool mutation(Pair&s,int budget,int upperCap){
 int side=rnd()&1;auto &a=s.arm[side],&b=s.arm[1-side];int n=a.size();
 if(n<4)return false;
 int mode=rnd()%100;int hi,lo;if(mode<33){hi=n-1;lo=max(0,hi-1-int(rnd()%35));}
 else {lo=rnd()%(n-2);int width=mode<68?2+rnd()%6:6+rnd()%25;hi=min(n-1,lo+width);}
 terminal=hi==n-1;dest=terminal?-1:a[hi];int cap=side?upperCap:96;
 ceiling=min(cap-(n-hi+lo-1),hi-lo+1+int(2+rnd()%9));
 threshold=max(2,hi-lo+1-(rnd()%16==0?2:0));
 endok.fill(true);deny.fill(0);
 for(int j=1;j<b.size();j++)deny[b[j]]++;
 if(side==0){int x=b.back();deny[x]++;for(int d=0;d<8;d++)deny[x^(1<<d)]++;}
 else for(int x:b){endok[x]=false;for(int d=0;d<8;d++)endok[x^(1<<d)]=false;}
 for(int j=0;j<n;j++)if(j<lo||j>hi){int x=a[j];deny[x]++;for(int d=0;d<8;d++)deny[x^(1<<d)]++;}
 deny[a[lo]]=0;if(dest>=0)deny[dest]=0;
 path={a[lo]};best=-1;ties=0;picked.clear();remain=budget;calls++;dfs(a[lo]);
 if(best<0)return false;vector<int>z(a.begin(),a.begin()+lo);z.insert(z.end(),picked.begin(),picked.end());z.insert(z.end(),a.begin()+hi+1,a.end());
 if(z==a)return false;a=move(z);changed++;return true;
}
int main(int argc,char**argv){assert(argc==6);ifstream f(argv[1]);int n,m;vector<Pair>pool;while(f>>n>>m){Pair p;p.arm[0].resize(n);p.arm[1].resize(m);for(auto&a:p.arm)for(int&x:a)f>>x;verify(p);pool.push_back(p);}
 seed=stoul(argv[2]);int runs=stoi(argv[3]),steps=stoi(argv[4]),upperCap=stoi(argv[5]),global=0;Pair champion;
 for(auto&s:pool)if(s.edges()>global){champion=s;global=s.edges();}save(champion,-1,-1);
 for(int run=0;run<runs;run++){int id=rnd()%pool.size();if(run%3){for(int z=0;z<3;z++){int j=rnd()%pool.size();if(pool[j].edges()>pool[id].edges())id=j;}}
 Pair s=pool[id],elite=s;int best=s.edges(),stale=0;
 for(int t=0;t<steps;t++){
   if(mutation(s,600+rnd()%2300,upperCap)){if(s.edges()>best){best=s.edges();elite=s;stale=0;if(best>global){global=best;champion=s;save(s,run,t);if(global>=192)return 0;}}
   else if(s.edges()==best&&rnd()%5==0)elite=s;}
   if(++stale>=70&&rnd()%17==0){s=elite;stale=0;}
 }
 if(best>=pool[id].edges())pool[id]=elite;
 if(run%100==99)cout<<"AT "<<run+1<<" best "<<global<<" nodes "<<nodes<<" calls "<<calls<<" admissible "<<finished<<" changed "<<changed<<endl;
 }cout<<"DONE "<<runs<<" "<<global<<" "<<nodes<<" "<<calls<<" "<<finished<<" "<<changed<<endl;}
