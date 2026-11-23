#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using namespace std;
using Bits=array<unsigned long long,4>;
bool has(const Bits&b,int v){return b[v/64]>>(v%64)&1;}
void put(Bits&b,int v){b[v/64]|=1ull<<(v%64);}
struct Forest{Bits b{};vector<int> vs,iso,ends;vector<vector<int>>longest;};
bool get(const Bits&b,Forest &f){
 f.b=b;array<int,256>deg{},seen{};int best=0,total=0;
 for(int v=0;v<256;v++)if(has(b,v)){
   f.vs.push_back(v);for(int d=0;d<8;d++)deg[v]+=has(b,v^1<<d);
   if(deg[v]>2)return false;if(!deg[v])f.iso.push_back(v);if(deg[v]==1)f.ends.push_back(v);
 }
 if(f.iso.size()>2)return false;
 for(int start:f.vs)if(deg[start]<2&&!seen[start]){
   vector<int>p;int v=start,prev=-1;
   while(v>=0){p.push_back(v);seen[v]=1;int next=-1;for(int j=0;j<8;j++){int u=v^1<<j;if(u!=prev&&has(b,u)){next=u;break;}}prev=v;v=next;}
   total+=p.size();if(p.size()>best){best=p.size();f.longest.clear();}if(p.size()==best)f.longest.push_back(p);
 }
 return total==f.vs.size()&&best;
}
Bits canonical(Forest&f){
 Bits best;best.fill(~0ull);
 for(auto p:f.longest)for(int rev=0;rev<2;rev++,reverse(p.begin(),p.end())){
    array<int,8> lab;lab.fill(-1);int next=0;
    for(int i=1;i<p.size();i++){int d=countr_zero(unsigned(p[i]^p[i-1]));if(lab[d]<0)lab[d]=next++;}
    vector<int> missing,free;for(int j=0;j<8;j++)if(lab[j]<0){missing.push_back(j);free.push_back(next++);}
    do{for(int j=0;j<missing.size();j++)lab[missing[j]]=free[j];
       int iso[256]{};for(int v=1;v<256;v++)iso[v]=iso[v&(v-1)]^1<<lab[countr_zero(unsigned(v))];
       Bits mask{};for(int v:f.vs)put(mask,iso[v^p[0]]);best=min(best,mask);
    }while(next_permutation(free.begin(),free.end()));
 }
 return best;
}
int main(int argc,char**argv){
 int coord=stoi(argv[1]),rows=0;map<Bits,vector<int>> unique;map<Bits,Bits> cache;
 string w;int valid=0;while(cin>>w){
    int x=0;vector<int>p{x};for(char c:w){x^=1<<(c-'0');p.push_back(x);}
    array<bool,512> used{};for(int v:p){if(used[v])return 2;used[v]=1;}
    for(int axis=0;axis<9;axis++)for(int side=0;side<2;side++){
       Bits layer{};for(int v:p)if(((v>>axis)&1)==side)put(layer,(v&((1<<axis)-1))|((v>>(axis+1))<<axis));
       auto it=cache.find(layer);Bits key{};
       if(it==cache.end()){Forest f;if(get(layer,f))key=canonical(f);cache[layer]=key;}else key=it->second;
       if(key==Bits{})continue;valid++;
       unique.try_emplace(key,vector<int>{rows,axis,side});
    }rows++;
 }
 cout<<"META "<<rows<<" "<<valid<<" "<<unique.size()<<endl;
 for(auto&[b,src]:unique){cout<<"F "<<coord<<" "<<src[0]<<" "<<src[1]<<" "<<src[2];for(auto u:b)cout<<" "<<u;cout<<'\n';}
}
