#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
using Bits=__uint128_t;
string canon(string w){
 auto norm=[](string z){int t[9],n=0;fill(t,t+9,-1);for(char& c:z){int a=c-'0';if(t[a]<0)t[a]=n++;c='0'+t[a];}return z;};
 auto a=norm(w);reverse(w.begin(),w.end());return min(a,norm(w));
}
int main(){string w;int i0,u,v,o;vector<string> input;map<string,array<int,5>> out;
 while(cin>>w>>i0>>u>>v>>o){input.push_back(w);out[w]={-1,0,0,0,0};}
 long long columnpairs=0,joined=0,admissible=0,pos=0;
 for(int id=0;id<(int)input.size();id++){
  w=input[id];vector<int> p={0};for(char c:w)p.push_back(p.back()^1<<(c-'0'));int n=p.size();
  int idx[512],ec[512]={};Bits hit[512]{};fill(idx,idx+512,-1);
  for(int i=0;i<n;i++){idx[p[i]]=i;for(int j=0;j<i;j++){int g=p[i]^p[j];ec[g]++;hit[g]|=(Bits(1)<<i)|(Bits(1)<<j);}}
  const Bits full=(Bits(1)<<n)-1;
  for(int a=0;a<9;a++)for(int b=a+1;b<9;b++){
   columnpairs++;int dirs[9];Bits occ=0,two=0;
   for(int k=0;k<9;k++){dirs[k]=1<<k;if(k!=a&&k!=b){int d=1<<k;two|=occ&hit[d];occ|=hit[d];}}
   int need=ec[1<<a]+ec[1<<b];vector<int> pool[4][128];
   for(int g=1;g<512;g++){
    if(g==(1<<a)||g==(1<<b)||ec[g]>need||ec[g]>=128||(hit[g]&two))continue;
    int q=((g>>a)&1)+2*((g>>b)&1);if(q)pool[q][ec[g]].push_back(g);
   }
   for(int c=1;c<=2;c++)for(int d=c+1;d<=3;d++)for(int f=0;f<=need;f++){
    if(need-f>=128||f>=128)continue;
    for(int g:pool[c][f])for(int h:pool[d][need-f]){joined++;Bits t=two|(occ&hit[g]);
     if(t&hit[h])continue;Bits all=occ|hit[g];t|=all&hit[h];all|=hit[h];if(all!=full)continue;
     Bits ends=all^t;if(__builtin_popcountll((uint64_t)ends)+__builtin_popcountll((uint64_t)(ends>>64))!=2)continue;
     admissible++;int start=(uint64_t)ends?__builtin_ctzll((uint64_t)ends):64+__builtin_ctzll((uint64_t)(ends>>64));int x=p[start],prev=-1;string path;dirs[a]=g;dirs[b]=h;
     for(;;){int nx=-1;for(int k=0;k<9;k++)if((x^dirs[k])!=prev&&idx[x^dirs[k]]>=0){nx=x^dirs[k];path.push_back(char('0'+k));break;}if(nx<0)break;prev=x;x=nx;}
     if((int)path.size()!=n-1)continue;pos++;
     auto word=canon(path);if(!out.count(word))out[word]={id,a,b,g,h};
    }
   }
  }
 }
 for(auto &[z,ref]:out)if(ref[0]>=0){cout<<z;for(int k:ref)cout<<" "<<k;cout<<"\n";}
 cerr<<"DONE "<<input.size()<<" "<<columnpairs<<" "<<joined<<" "<<admissible<<" "<<pos<<" "<<out.size()-input.size()<<endl;
}
