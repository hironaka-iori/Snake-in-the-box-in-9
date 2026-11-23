#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <vector>
using namespace std;using LL=long long;
struct Axis{int mask;array<int,8>expand{};array<int,256>compress{};array<array<int,8>,256>price{};};
struct Cert{int scale,fees[2],balance;vector<Axis> axes;};
struct Pattern{int on;array<int,8> sig{};};
vector<Pattern>patterns;vector<string> words;
void init(){for(int z=0;z<256;z++){Pattern p{z};int un=z;bool ok=true;for(int i=0;i<8;i++)if(z>>i&1)for(int d=0;d<3;d++)p.sig[i]|=((z>>(i^(1<<d)))&1)<<d;
 while(un){int first=countr_zero(unsigned(un)),todo=1<<first,comp=0,ds=0;while(todo){int v=countr_zero(unsigned(todo));todo^=1<<v;if(comp>>v&1)continue;comp|=1<<v;ds+=popcount(unsigned(p.sig[v]));for(int d=0;d<3;d++)if(p.sig[v]>>d&1)todo|=(1<<(v^(1<<d)))&~comp;}
 if(ds>=2*popcount(unsigned(comp))){ok=false;break;}un&=~comp;}if(ok)patterns.push_back(p);}}
LL finalFee,finalBal;
LL score(int donor,int extra,const Cert&c,bool refine=false){
 int orient=extra/256;extra%=256;vector<int> seq{0};for(char d:words[donor])seq.push_back(seq.back()^(1<<(d-'0')));
 array<bool,256>low{},port{},pool{};int lowerSum=0,m=popcount(unsigned(extra))%2;
 for(int i=0;i<seq.size();i++){int u=seq[i];assert(!low[u]&&popcount(unsigned(extra^u))>1);low[u]=1;for(int j=0;j<i;j++)assert((popcount(unsigned(seq[j]^u))==1)==(i==j+1));}
 int other=orient?seq.front():seq.back();low[extra]=1;port[extra]=port[orient?seq.back():seq.front()]=1;
 for(int q=0;q<256;q++){pool[q]=!low[q]||port[q];if(low[q])lowerSum+=1-2*(popcount(unsigned(q))%2);}
 lowerSum-=(2-2*m-2*(popcount(unsigned(other))%2))/2;
 LL out=LL(c.scale)*(seq.size()+1)+LL(lowerSum)*c.balance;
 vector<array<unsigned char,256>> sig(c.axes.size());
 array<LL,256>A{},B{};A.fill(-10000000000LL);B.fill(-10000000000LL);
 for(int v=0;v<256;v++)if(pool[v]){int allowed=0;for(int d=0;d<8;d++)if(pool[v^(1<<d)])allowed|=1<<d;
  LL best=port[v]?-1000000000000LL:0;int p=popcount(unsigned(v))%2;
  for(int s=allowed;;s=(s-1)&allowed){int degree=popcount(unsigned(s))+port[v];
   if(degree==2){LL val=c.scale-(1-2*p)*c.balance;
    for(int k=0;k<c.axes.size();k++){int z=c.axes[k].compress[s];val+=c.axes[k].price[v][z];sig[k][v]|=1<<z;}best=max(best,val);
     LL raw=val+(1-2*p)*c.balance+(degree==1?c.fees[1-m]:0);
     if(degree==1)B[v]=max(B[v],raw);else A[v]=max(A[v],raw);}
   if(!s)break;
  }assert(best>-1000000000000LL);out+=best;
 }
 for(int k=0;k<c.axes.size();k++){auto &a=c.axes[k];for(int b=0;b<256;b++)if(!(b&a.mask)){
  int forbidden=0,forced=0;for(int j=0;j<8;j++){int v=b^a.expand[j];if(!pool[v])forbidden|=1<<j;if(port[v])forced|=1<<j;}
  LL best=-1000000000000LL;for(auto &p:patterns)if(!(p.on&forbidden)&&(p.on&forced)==forced){
   LL val=0;bool ok=true;for(int on=p.on;on;on&=on-1){int i=countr_zero(unsigned(on)),v=b^a.expand[i],z=p.sig[i];if(!((sig[k][v]>>z)&1)){ok=false;break;}val-=a.price[v][z];}
   if(ok)best=max(best,val);
  }assert(best>-1000000000000LL);out+=best;
 }}
 if(refine){
  auto cost=[&](LL lambda, bool optimal, LL explicitFee){
   LL f=-10000000000LL;array<LL,256>norm{},end{};
   for(int v=0;v<256;v++)if(pool[v]){
    int sg=1-2*(popcount(unsigned(v))%2);norm[v]=A[v]-sg*lambda;if(!port[v])norm[v]=max(0LL,norm[v]);end[v]=B[v]-sg*lambda;
    if(B[v]>-9000000000LL&&norm[v]>-9000000000LL)f=max(f,end[v]-norm[v]);
   }
   if(f< -9000000000LL)f=0;if(!optimal)f=explicitFee;
   f=0;LL val=lambda*lowerSum;for(int v=0;v<256;v++)if(pool[v])val+=max(norm[v],end[v]-f);
   return pair<LL,LL>{val,f};
  };
  LL l=-30LL*c.scale,r=30LL*c.scale;
  while(l<r){LL t=l+(r-l)/2;if(cost(t,true,0).first<=cost(t+1,true,0).first)r=t;else l=t+1;}
  auto [newCost,f]=cost(l,true,0);LL oldCost=cost(c.balance,false,0).first;
  finalBal=l;finalFee=f;out+=newCost-oldCost;
 }
 return out;
}
int main(int argc,char**argv){assert(argc==2);ifstream f(argv[1]);string w;while(f>>w)words.push_back(w);init();map<int,Cert>bank;char op;
 while(cin>>op){if(op=='C'){int id,na,nw;cin>>id;auto&c=bank[id];cin>>c.scale>>c.fees[0]>>c.fees[1]>>c.balance>>na>>nw;assert(c.scale>0&&na<=56);c.axes.resize(na);map<int,int>index;
 for(int k=0;k<na;k++){auto&a=c.axes[k];cin>>a.mask;assert(popcount(unsigned(a.mask))==3&&!index.count(a.mask));index[a.mask]=k;int d[3],t=0;for(int i=0;i<8;i++)if(a.mask>>i&1)d[t++]=i;
  for(int z=0;z<8;z++)for(int i=0;i<3;i++)if(z>>i&1)a.expand[z]|=1<<d[i];for(int s=0;s<256;s++)for(int i=0;i<3;i++)a.compress[s]|=((s>>d[i])&1)<<i;
 }
 for(int n=0;n<nw;n++){int g,v,s,p;cin>>g>>v>>s>>p;assert(index.count(g)&&v>=0&&v<256&&(s&~g)==0);auto&a=c.axes[index[g]];a.price[v][a.compress[s]]=p;}}
 else{assert(op=='Q'||op=='T');int id,i,x;cin>>id>>i>>x;cout<<id<<" "<<i<<" "<<x<<" "<<score(i,x,bank.at(id),op=='T');if(op=='T')cout<<" "<<finalFee<<" "<<finalBal;cout<<"\n";}}
}
