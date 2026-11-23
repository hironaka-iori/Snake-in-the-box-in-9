#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <map>
using namespace std;
using W=__uint128_t;
int wt(int a){return __builtin_popcount((unsigned)a);}
string norm(string w){
 int table[9],k=0;fill(table,table+9,-1);
 for(char& c:w){int a=c-'0';if(table[a]<0)table[a]=k++;c='0'+table[a];}return w;
}
string canon(string w){auto a=norm(w);reverse(w.begin(),w.end());return min(a,norm(w));}
struct Prov{int idx,u,v,orig;};
int main(int argc,char**argv){
 if(argc!=2)return 2;int d=atoi(argv[1]),N=1<<d;
 map<string,Prov> bank;long long tried=0,accepted=0,changed=0,alteredEnds=0,inspected=0;
 string w;int id=-1;
 while(cin>>w){id++;int n=w.size()+1;if(n>=128)return 3;
  vector<int> pts(1,0);int used=0;for(char c:w){int g=1<<(c-'0');pts.push_back(pts.back()^g);used|=g;}
  auto input=canon(w);auto it=bank.find(input);if(it==bank.end())bank.emplace(input,Prov{id,0,0,1});else it->second.orig=1;
  array<int,512> index,edges{};index.fill(-1);array<W,512> touch{};
  for(int i=0;i<n;i++){index[pts[i]]=i;for(int j=0;j<i;j++){
    int g=pts[i]^pts[j];edges[g]++;touch[g]|=(W(1)<<i)|(W(1)<<j);
  }}
  for(int u=1;u<N;u++){
   int delta[9],broken=0;for(int i=0;i<d;i++){int g=(1<<i)^u;delta[i]=edges[g]-edges[1<<i];if(wt(g)!=1)broken|=(1<<i);}
   int sum[512]={};
   for(int v=1;v<N;v++){sum[v]=sum[v&(v-1)]+delta[__builtin_ctz(v)];
    if(__builtin_parity((unsigned)(v&u)))continue;
    tried++;if(sum[v]||!(v&broken&used))continue;
    inspected++;int directions[9];W one=0,two=0;bool good=true;
    for(int i=0;i<d;i++){int g=(1<<i)^((v>>i&1)?u:0);directions[i]=g;W hit=touch[g];
      if(two&hit){good=false;break;}two|=one&hit;one|=hit;}
    if(!good||one!=((W(1)<<n)-1))continue;
    W ends=one^two;int endsN=__builtin_popcountll((uint64_t)ends)+__builtin_popcountll((uint64_t)(ends>>64));if(endsN!=2)continue;
    int start=(uint64_t)ends?__builtin_ctzll((uint64_t)ends):64+__builtin_ctzll((uint64_t)(ends>>64));
    int x=pts[start],prev=-1;string order;
    for(;;){int nx=-1;for(int i=0;i<d;i++){int y=x^directions[i];if(y!=prev&&index[y]!=-1){nx=y;order.push_back(char('0'+i));break;}}
      if(nx<0)break;prev=x;x=nx;if((int)order.size()>=n)abort();}
    if((int)order.size()!=n-1)continue;
    accepted++;auto k=canon(order);if(k!=input)changed++;if(start!=0||index[x]!=n-1)if(start!=n-1||index[x]!=0)alteredEnds++;
    auto f=bank.find(k);if(f==bank.end())bank.emplace(k,Prov{id,u,v,0});
    else if(!f->second.u){f->second.idx=id;f->second.u=u;f->second.v=v;}
   }
  }
  if((id+1)%400==0)cerr<<"AT "<<id+1<<" "<<bank.size()<<endl;
 }
 for(auto &e:bank)cout<<e.first<<" "<<e.second.idx<<" "<<e.second.u<<" "<<e.second.v<<" "<<e.second.orig<<"\n";
 cerr<<"DONE "<<id+1<<" "<<tried<<" "<<inspected<<" "<<accepted<<" "<<changed<<" "<<alteredEnds<<" "<<bank.size()<<endl;
}
