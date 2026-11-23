#define Q9_GRAY_LIBRARY
#include "search_q9_q5_gray.cpp"
using StateBits=array<uint64_t,6>;
int main(int argc,char**argv){
 Runner r(0,1,1);r.init();int n=rep.size();
 array<StateBits,15> lengths{};vector<array<StateBits,15>> next(n);
 for(int i=0;i<n;i++){
  lengths[rows[rep[i]].n][i/64]|=uint64_t(1)<<(i%64);
  for(int j:r.lengths[i])next[i][rows[rep[j]].n][j/64]|=uint64_t(1)<<(j%64);
 }
 map<pair<StateBits,int>,StateBits> table;
 long long tested=0,capacityFailed=0,adjacentFailed=0,failedRows=0;string w;
 while(cin>>w){int failures=0;
  for(int m=0;m<512;m++)if(popcount(unsigned(m))==4){
   int layer=0;vector<int>lens{1};array<int,512> points{},visits{};points[0]=visits[0]=1;
   for(char c:w){int t=1<<(c-'0');if(t&m){layer^=t;visits[layer]++;lens.push_back(1);}else lens.back()++;points[layer]++;}
   bool cap=false;for(int j=0;j<512;j++)if(visits[j]){
     int bound=visits[j]<=2?14:visits[j]==3?15:16;if(points[j]>bound){cap=true;break;}
   }tested++;if(cap){capacityFailed++;failures++;continue;}
   StateBits active{};bool first=true,bad=false;
   for(int len:lens){
    if(len>14){bad=true;break;}
    if(first){active=lengths[len];first=false;}
    else{
     auto key=make_pair(active,len);auto it=table.find(key);
     if(it==table.end()){StateBits out{};
      for(int part=0;part<6;part++)for(auto rem=active[part];rem;rem&=rem-1){
       auto &add=next[part*64+countr_zero(rem)][len];for(int j=0;j<6;j++)out[j]|=add[j];}
      it=table.emplace(key,out).first;
     }active=it->second;
    }
    if(all_of(active.begin(),active.end(),[](uint64_t x){return !x;})){bad=true;break;}
   }
   if(bad){adjacentFailed++;failures++;}
  }failedRows+=failures>0;
 }cout<<"DONE projections "<<tested<<" capacity_impossible "<<capacityFailed<<" additional_run_length_impossible "<<adjacentFailed<<" affected_words "<<failedRows<<endl;
}
