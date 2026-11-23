#define main generate_catalogue
#include "q7_extreme_interfaces.cpp"
#undef main
using M=__uint128_t;
M bit(int v){return M(1)<<v;}
int count(M a){return __builtin_popcountll((U)a)+__builtin_popcountll((U)(a>>64));}
M shiftmask[7];
M translate(M a,int d){int k=1<<d;return ((a&shiftmask[d])<<k)|((a&~shiftmask[d])>>k);}
int main(){
 unsigned long long a,b;vector<M> sites,ends;vector<array<int,128>> labels;
 while(scanf("%llx %llx",&a,&b)==2){
  Layout m={a,b};M s=M(a)|(M(b)<<64),e=0;
  array<int,128> lab{};int nc=0;
  for(auto p:paths(m,7))if(p[0]<p[13]){
   e|=bit(p[0])|bit(p[13]);for(int x:p)lab[x]=nc;++nc;}
  if(nc!=4 ||count(e)!=8)abort();
  sites.push_back(s);ends.push_back(e);labels.push_back(lab);
 }
 for(int d=0;d<7;d++)for(int x=0;x<128;x++)if(!(x&(1<<d)))shiftmask[d]|=bit(x);
 unsigned long long hist[9]={},foresthist[9]={};int types=sites.size();
 for(int i=0;i<types;i++){
  array<int,7> pm={0,1,2,3,4,5,6};
  do{
   M s=0,e=0;int inv[128];int mp[128]={};
   for(int x=0;x<128;x++){
    if(x)mp[x]=mp[x&(x-1)]|(1<<pm[__builtin_ctz(x)]);
    inv[mp[x]]=x;
    if(sites[i]&bit(x))s|=bit(mp[x]);if(ends[i]&bit(x))e|=bit(mp[x]);
   }
   for(int n=0;n<128;n++){
    int t=n^(n>>1);
    if(n){int d=__builtin_ctz(n);s=translate(s,d);e=translate(e,d);}
    for(int j=0;j<types;j++){
     M ov=s&sites[j];if(ov & ~(e&ends[j]))continue;
     int k=count(ov);++hist[k];
     if(!k){++foresthist[k];continue;}
     int par[8]={0,1,2,3,4,5,6,7};bool good=true;
     while(ov){
      int x=(U)ov?__builtin_ctzll((U)ov):64+__builtin_ctzll((U)(ov>>64));ov&=ov-1;
      int l=labels[i][inv[x^t]],r=4+labels[j][x];
      while(l!=par[l])l=par[l];while(r!=par[r])r=par[r];if(l==r){good=false;break;}par[l]=r;
     }
     if(good)++foresthist[k];
    }
   }
  }while(next_permutation(pm.begin(),pm.end()));
 }
 printf("classes %d relative placements %llu\n",types,(unsigned long long)types*types*5040*128);
 for(int k=0;k<=8;k++)printf("cross %d degree_valid %llu forest_valid %llu\n",k,hist[k],foresthist[k]);
}

