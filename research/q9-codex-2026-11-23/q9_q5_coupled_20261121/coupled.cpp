#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;using U=uint32_t;
struct R{U m;int t,n;};vector<R> rows;
vector<int> cat[32],longcat[32];vector<U> shifted[32];U nbs[32],seed=17368473;
U rnd(){seed^=seed<<13;seed^=seed>>17;seed^=seed<<5;return seed;}
float uniform(){return (rnd()+0.5)*2.3283064365386963e-10;}
U shift(U m,int t){if(t&1)m=((m&0x55555555u)<<1)|((m&0xaaaaaaaau)>>1);if(t&2)m=((m&0x33333333u)<<2)|((m&0xccccccccu)>>2);if(t&4)m=((m&0x0f0f0f0fu)<<4)|((m&0xf0f0f0f0u)>>4);if(t&8)m=((m&0x00ff00ffu)<<8)|((m&0xff00ff00u)>>8);if(t&16)m=rotl(m,16);return m;}
void gen(int x,U m,U ban){int id=rows.size(),n=popcount(m);rows.push_back({m,x,n});cat[x].push_back(id);if(n>=10)longcat[x].push_back(id);
 for(U s=nbs[x]&~(ban|m);s;s&=s-1){int y=countr_zero(s);gen(y,m|(1u<<y),ban|nbs[x]);}}
struct State{array<U,16> m{};array<int,17>p{};};
int adj[16][4],gray[16];uint64_t valid=0,moves=0;
struct E{int n=0,c=-15;};
E eval(const State&s){E e;for(int k=0;k<16;k++){e.n+=popcount(s.m[k]);for(int d=0;d<4;d++)if(adj[k][d]<k)e.c+=popcount(s.m[k]&s.m[adj[k][d]]);}return e;}
void choose(State&s,int k,float lam,int samples){
 int root=s.p[k],diff=root^s.p[k+1];auto&all=cat[diff];auto&lg=longcat[diff];
 int best=-99999;U picked=0;int li=12*lam;
 for(int i=0;i<samples;i++){auto&v=(!lg.empty()&&(rnd()&3))?lg:all;int id=v[rnd()%v.size()];
  U mask=shifted[root][id];int c=0;for(int d=0;d<4;d++)c+=popcount(mask&s.m[adj[k][d]]);
  int val=12*rows[id].n-li*c+int(rnd()%22);if(val>best){best=val;picked=mask;}}
 s.m[k]=picked;
}
void writeBest(const State&s,const string&order,int id,int it){
 auto e=eval(s);vector<int>path;for(int k=0;k<16;k++){U m=s.m[k];int x=s.p[k];for(;;){path.push_back(gray[k]*32+x);m^=1u<<x;if(!m)break;U next=nbs[x]&m;if(!has_single_bit(next))abort();x=countr_zero(next);}if(x!=s.p[k+1])abort();}
 for(int i=0;i<path.size();i++)for(int j=0;j<i;j++)if(path[i]==path[j]||has_single_bit(unsigned(path[i]^path[j]))!=(j+1==i))abort();
 cout<<"BEST "<<e.n-1<<" "<<order<<" "<<id<<" "<<it;for(int x:path)cout<<" "<<x;cout<<endl;
}
int main(int argc,char**argv){
 if(argc!=6)return 2;ifstream f(argv[1]);vector<string> orders;string w;while(f>>w)orders.push_back(w);
 seed=stoul(argv[2]);int rounds=stoi(argv[3]),steps=stoi(argv[4]),offset=stoi(argv[5]);
 for(int x=0;x<32;x++)for(int d=0;d<5;d++)nbs[x]|=1u<<(x^(1<<d));gen(0,1,0);if(rows.size()!=41186)abort();
 for(int x=0;x<32;x++)for(auto r:rows)shifted[x].push_back(shift(r.m,x));
 int global=0;vector<State> elites(orders.size());vector<int> records(orders.size());int maxRaw=0,minBad=999;
 for(int run=0;run<rounds;run++){int id=(offset+run*37)%int(orders.size());auto order=orders[id];gray[0]=0;
  int ix[16];for(int k=0;k<15;k++)gray[k+1]=gray[k]^(1<<(order[k]-'0'));for(int k=0;k<16;k++)ix[gray[k]]=k;
  for(int k=0;k<16;k++)for(int d=0;d<4;d++)adj[k][d]=ix[gray[k]^(1<<d)];
  State s;for(int k=0;k<17;k++)s.p[k]=rnd()%32;for(int k=0;k<16;k++)choose(s,k,2,100);
  if(records[id]&&rnd()%5)s=elites[id];E old=eval(s);int local=0;
  for(int it=0;it<steps;it++){
   float phase=float(it%25000)/25000,lam=3+9*phase,T=2.8f*(1-phase)+0.22f;State t=s;
   int a=rnd()%16,kind=rnd()%100;
   if(kind<53){choose(t,a,lam,36);}
   else if(kind<63){int k=(rnd()&1)?0:16;t.p[k]=rnd()%32;choose(t,k?15:0,lam,40);}
   else{
    int b=min(15,a+1+int(rnd()%(kind<89?1:7)));if(b==a){a--;}
    int delta=(rnd()%3==0)?1<<(rnd()%5):1+rnd()%31;
    for(int k=a+1;k<=b;k++)t.p[k]^=delta;
    for(int k=a+1;k<b;k++)t.m[k]=shift(t.m[k],delta);
    t.m[a]=t.m[b]=0;if(rnd()&1){choose(t,a,lam,36);choose(t,b,lam,42);}else{choose(t,b,lam,36);choose(t,a,lam,42);}
   }
   moves++;E e=eval(t);float gain=e.n-old.n-lam*(e.c-old.c);if(gain>=0||uniform()<expf(gain/T)){s=t;old=e;}
   if(!e.c){valid++;local=max(local,e.n-1);if(e.n>records[id]){records[id]=e.n;elites[id]=t;}
    if(e.n-1>global){global=e.n-1;writeBest(t,order,run,it);if(global>=192)return 0;}}
   if(e.n>=193)minBad=min(minBad,e.c);
   if(it%25000==24999&&records[id]&&rnd()%3)s=elites[id],old=eval(s);
  }
  cout<<"RUN "<<run<<" "<<id<<" "<<local<<" "<<global<<" "<<valid<<" "<<moves<<" "<<minBad<<endl;
 }
}
