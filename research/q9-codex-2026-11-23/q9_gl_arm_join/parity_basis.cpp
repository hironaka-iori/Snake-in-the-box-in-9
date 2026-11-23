#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using namespace std;using Bits=__uint128_t;
string canon(string w){auto norm=[](string z){int tab[9],n=0;fill(tab,tab+9,-1);for(char& c:z){int a=c-'0';if(tab[a]<0)tab[a]=n++;c='0'+tab[a];}return z;};auto z=norm(w);reverse(w.begin(),w.end());return min(z,norm(w));}
struct Job{
 int K,n,id,dim=0,ec[512]{},pos[512],dirs[9],drop[9],take[9];Bits hit[512]{},full;vector<int> pts{0},candidates;map<string,vector<int>>& out;long long nodes=0,leaves=0,snakes=0;
 Job(string w,int k,int index,map<string,vector<int>>& shared):K(k),id(index),out(shared){
  for(char c:w){int a=c-'0';dim=max(dim,a+1);pts.push_back(pts.back()^1<<a);}n=pts.size();full=(Bits(1)<<n)-1;fill(pos,pos+512,-1);
  for(int i=0;i<n;i++){pos[pts[i]]=i;for(int j=0;j<i;j++){int g=pts[i]^pts[j];ec[g]++;hit[g]|=(Bits(1)<<i)|(Bits(1)<<j);}}
 }
 void finish(Bits seen,Bits two){
  if(seen!=full)return;Bits ends=seen^two;int m=__builtin_popcountll((uint64_t)ends)+__builtin_popcountll((uint64_t)(ends>>64));if(m!=2)return;
  leaves++;int start=(uint64_t)ends?__builtin_ctzll((uint64_t)ends):64+__builtin_ctzll((uint64_t)(ends>>64));int x=pts[start],prev=-1;string w;
  for(int i=0;i<K;i++)dirs[drop[i]]=take[i];
  for(;;){int nx=-1;for(int k=0;k<dim;k++)if((x^dirs[k])!=prev&&pos[x^dirs[k]]>=0){nx=x^dirs[k];w.push_back(char('0'+k));break;}if(nx<0)break;prev=x;x=nx;}
  if((int)w.size()!=n-1)return;snakes++;string key=canon(w);if(!out.count(key)){vector<int> ref{id};for(int j=0;j<9;j++)ref.push_back(dirs[j]);out.emplace(key,ref);}
 }
 int quotient[512]{},chosen[9]{};long long cap;
 void dfs(int lo,int depth,int remaining,Bits occ,Bits two){
  if(nodes>=cap)return;nodes++;
  if(depth==K){if(!remaining)finish(occ,two);return;}
  int left=K-depth;
  for(int i=lo;i+left<=(int)candidates.size();i++){
   int g=candidates[i],w=ec[g];if(w*left<remaining)break;
   if(w>remaining || (hit[g]&two))continue;
   if(left==1&&w!=remaining)continue;
   int q=quotient[g];for(int z=0;z<depth;z++)q=min(q,q^chosen[z]);if(!q)continue;chosen[depth]=q;
   take[depth]=g;dfs(i+1,depth+1,remaining-w,occ|hit[g],two|(occ&hit[g]));if(nodes>=cap)return;
  }
 }
 void run(long long limit){cap=limit;
  vector<int> forms;
  for(int c=1;c<(1<<dim);c++){int cnt=0;for(int x:pts)cnt+=__builtin_parity((unsigned)(x&c));if(abs(n-2*cnt)<=1)forms.push_back(c);}
  for(int k=0;k<9;k++)dirs[k]=1<<k;
  for(int mask=1;mask<(1<<dim)&&nodes<cap;mask++)if(__builtin_popcount((unsigned)mask)==K){
   int need=0,m=0;Bits occ=0,two=0;for(int j=0;j<dim;j++){dirs[j]=1<<j;
    if(mask>>j&1){drop[m++]=j;need+=ec[1<<j];}else{auto h=hit[1<<j];two|=occ&h;occ|=h;}}
   for(int parity:forms){if(nodes>=cap)break;if(((~parity)&(~mask)&((1<<dim)-1))!=0)continue;candidates.clear();
   for(int g=1;g<(1<<dim);g++){if(!ec[g]||!__builtin_parity((unsigned)(parity&g))||!(g&mask)||!(g&(g-1))||ec[g]>need||(two&hit[g]))continue;
    int q=0;for(int j=0;j<K;j++)if(g>>drop[j]&1)q|=1<<j;
    
    quotient[g]=q;candidates.push_back(g);}
   sort(candidates.begin(),candidates.end(),[&](int a,int b){return ec[a]>ec[b]||(ec[a]==ec[b]&&a<b);});
   dfs(0,0,need,occ,two);}
  }
 }
};
int main(int argc,char**argv){int K=atoi(argv[1]);if(K<1||K>9)return 2;long long cap=atoll(argv[2]);int lo=atoi(argv[3]),hi=atoi(argv[4]),i0,u,v,o;string w;vector<string> input;map<string,vector<int>> out;
 while(cin>>w>>i0>>u>>v>>o){input.push_back(w);out[w]={};}
 long long nodes=0,leaves=0,valid=0,capped=0,ran=0;
 for(int id=lo;id<min(hi,(int)input.size());id++){Job s(input[id],K,id,out);s.run(cap);nodes+=s.nodes;leaves+=s.leaves;valid+=s.snakes;capped+=s.nodes>=cap;ran++;if(s.nodes>=cap)cerr<<"LIMIT "<<id<<endl;
 if(ran%1000==0)cerr<<"AT "<<id+1<<" "<<nodes<<" "<<out.size()-input.size()<<endl;}
 for(auto &[key,ref]:out)if(!ref.empty()){cout<<key;for(int z:ref)cout<<" "<<z;cout<<"\n";}
 cerr<<"DONE "<<K<<" "<<ran<<" "<<nodes<<" "<<leaves<<" "<<valid<<" "<<capped<<" "<<out.size()-input.size()<<endl;
}
