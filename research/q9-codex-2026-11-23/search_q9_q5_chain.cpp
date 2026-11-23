// Each Q5 layer is visited in one contiguous run. Relax every contact except
// between consecutive layers, while requiring their one shared column be the tip.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <vector>
using namespace std;
using U=uint32_t;
struct Row{U mask;int end,n,shape;};
array<U,32> nb{};
vector<Row> rows;
vector<int> rep;
map<pair<U,int>,int> label;
vector<array<int,32>> group;
void collect(int x,U on,U banned){
 int id;
 auto it=label.find({on,x});
 if(it==label.end()){
    id=rep.size();rep.push_back(rows.size());
    for(const auto &perm:group){
      U shape=0;for(U s=on;s;s&=s-1)shape|=U(1)<<perm[countr_zero(s)];
      label.emplace(make_pair(shape,perm[x]),id);
    }
 }else id=it->second;
 rows.push_back({on,x,popcount(on),id});
 for(U s=nb[x]&~(on|banned);s;s&=s-1){
  int y=countr_zero(s);collect(y,on|(U(1)<<y),banned|nb[x]);
 }
}
U translate(U x,int t){U y=0;while(x){int b=countr_zero(x);y|=U(1)<<(b^t);x&=x-1;}return y;}
int main(int argc,char**argv){
 for(int x=0;x<32;x++)for(int d=0;d<5;d++)nb[x]|=U(1)<<(x^(1<<d));
 array<int,5>p{0,1,2,3,4};do{
  array<int,32> img{};for(int x=1;x<32;x++)img[x]=img[x&(x-1)]|(1<<p[countr_zero(unsigned(x))]);group.push_back(img);
 }while(next_permutation(p.begin(),p.end()));
 collect(0,1,0);cout<<"ROWS "<<rows.size()<<" symmetry_types "<<rep.size()<<endl;
 vector<vector<int>> adj(rep.size());
 for(int i=0;i<rep.size();i++){
   const auto &a=rows[rep[i]];U block=translate(a.mask,a.end)&~U(1);
   vector<bool> present(rep.size());for(auto &b:rows)if(!(b.mask&block))present[b.shape]=true;
   for(int j=0;j<rep.size();j++)if(present[j])adj[i].push_back(j);
 }
 vector<int> value(rep.size()),next(rep.size());
 for(int n=1;n<=16;n++){
   for(int i=0;i<rep.size();i++){
      int m=0;for(int j:adj[i])m=max(m,value[j]);next[i]=rows[rep[i]].n+m;
   }value.swap(next);
   cout<<"MAX "<<n<<" Q5 slices "<<*max_element(value.begin(),value.end())<<" vertices"<<endl;
 }
return 0;
}
