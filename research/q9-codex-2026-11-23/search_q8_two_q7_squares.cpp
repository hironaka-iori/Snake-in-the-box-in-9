#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Arm{string w;vector<int>p;array<uint64_t,2> mask{};};
int main(int argc,char**argv){
 if(argc!=2&&argc!=3)return 2;int cutoff=stoi(argv[1]),lower=argc==3?stoi(argv[2]):47;
 vector<Arm> bank[51];string w;
 while(cin>>w){Arm r{w,{0}};for(char c:w)r.p.push_back(r.p.back()^(1<<(c-'0')));
  for(int i=0;i<r.p.size();i++){int x=r.p[i];if((r.mask[x/64]>>(x%64))&1)abort();r.mask[x/64]|=uint64_t(1)<<(x%64);
   for(int j=0;j<i;j++)if(has_single_bit(unsigned(x^r.p[j]))!=(j+1==i))abort();}
  bank[r.p.size()].push_back(std::move(r));
 }
 array<int,5>perm{0,1,2,3,4};uint64_t tests[101]{},found[101]{};
 do{for(int swap=0;swap<2;swap++){
   int img[128]{};for(int v=1;v<128;v++){int d=countr_zero(unsigned(v));img[v]=img[v&(v-1)]|(1<<(d<5?perm[d]:swap?11-d:d));}
   for(int a=lower;a<=50;a++)for(int b=lower;b<=a;b++)if(a+b>=cutoff&&(argc==2||b==lower)){
    for(const auto &right:bank[b]){
     uint64_t mask[2]{};for(int x:right.p)if(x){int y=img[x];mask[y/64]|=uint64_t(1)<<(y%64);}
     tests[a+b]+=bank[a].size();
     for(const auto&left:bank[a]){
      if((mask[0]&left.mask[0])||(mask[1]&left.mask[1]))continue;
      if(!found[a+b]++){
       vector<int> q(left.p.rbegin(),left.p.rend());for(int x:right.p)q.push_back(128+img[x]);
       for(int i=0;i<q.size();i++)for(int j=0;j<i;j++)if(q[i]==q[j]||has_single_bit(unsigned(q[i]^q[j]))!=(i==j+1))abort();
       cout<<"WITNESS "<<a+b<<" vertices";for(int x:q)cout<<" "<<x;cout<<endl;
      }
     }
    }
   }
 }}while(next_permutation(perm.begin(),perm.end()));
 for(int i=cutoff;i<=100;i++)cout<<"DONE "<<i<<" vertices "<<tests[i]<<" tests "<<found[i]<<" compatible"<<endl;
}
