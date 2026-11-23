// Permute one coordinate face internally by translation, allowing the snake
// to cross its boundary many times. Retain complete stretched transitions.
#define main geodesic_cli
#include "search_q9_sheared_geodesics.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=5)return 2;int target=stoi(argv[1]),rank=stoi(argv[2]),h=stoi(argv[3]),stride=stoi(argv[4]);
 string w;int rows=0;uint64_t maps=0,windows=0,capped=0;
 while(cin>>w){
  vector<int> src{0};for(char c:w){if(c<'0'||c>'8')abort();src.push_back(src.back()^(1<<(c-'0')));}
  int n=src.size();vector<int> v(n),cost(n);
  for(int mask=1;mask<512;mask++)if(popcount(unsigned(mask))==rank){
   int free=511^mask;
   for(int off=mask;;off=(off-1)&mask){
    for(int shift=free;shift;shift=(shift-1)&free)if(popcount(unsigned(shift))==h){
     uint64_t key=(((uint64_t(rows)*521+mask)*521+off)*521+shift)*11400714819323198485ull;
     if((key^(key>>33))%stride)continue;
     maps++;array<int,512> when;when.fill(-1);int s=0;
     for(int j=0;j<n;j++){
      int x=src[j];if((x&mask)==off)x^=shift;v[j]=x;
      s=max(s,when[x]+1);
      for(int d=0;d<9;d++){int i=when[x^(1<<d)];if(i!=j-1)s=max(s,i+1);}
      when[x]=j;if(j)cost[j]=cost[j-1]+popcount(unsigned(v[j]^v[j-1]));
      int a=upper_bound(cost.begin()+s,cost.begin()+j+1,cost[j]-target)-cost.begin()-1;
      if(a<s||a>=j||cost[j-1]-cost[a]>=target)continue;
      windows++;Scan test;test.limit=20000;
      if(test.run(v,a,j)){cout<<"PARAM "<<rows<<" "<<mask<<" "<<off<<" "<<shift<<" "<<a<<" "<<j<<endl;return 0;}
      if(test.capped){capped++;cout<<"CAPPED";for(int x:test.anchors)cout<<" "<<x;cout<<endl;}
     }
    }if(off==0)break;
   }
  }
  if(++rows%50==0)cout<<"AT "<<rows<<" "<<maps<<" "<<windows<<" "<<capped<<endl;
 }
 cout<<"DONE "<<rows<<" "<<maps<<" "<<windows<<" "<<capped<<endl;
}
