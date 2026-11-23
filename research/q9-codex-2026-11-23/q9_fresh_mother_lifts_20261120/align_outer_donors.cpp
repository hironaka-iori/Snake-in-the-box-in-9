#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
using Mask=array<uint64_t,4>; using Path=vector<int>;
void add(Mask& m,int v){m[v>>6]|=1ULL<<(v&63);}
struct Mother{string w;Path path;Mask blocked{};int score=257;Path best;};
bool valid(const Path&p){
 for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){
  int d=popcount(unsigned(p[i]^p[j]));if(d==0||((d==1)!=(j+1==i)))return false;
 }return true;
}
int lengthen(Path&p,int goal){
 if(int(p.size())-1>=goal)return true;
 for(int side=0;side<2;side++){
  reverse(p.begin(),p.end());
  for(int d=0;d<9;d++){
   int v=p.back()^(1<<d);bool ok=true;
   for(int i=0;i+1<p.size();i++)if(popcount(unsigned(v^p[i]))<=1){ok=false;break;}
   if(ok){p.push_back(v);if(lengthen(p,goal))return true;p.pop_back();}
  }
 }
 return false;
}
int main(int argc,char**argv){
 ifstream donorfile(argv[1]);ofstream nearfile(argv[2]);
 array<vector<Mother>,256> buckets;string w;
 while(cin>>w){
  Mother s; s.w=w;s.path={0};for(char c:w)s.path.push_back(s.path.back()^(1<<(c-'0')));
  assert(valid(s.path));for(int j=1;j+1<s.path.size();j++)add(s.blocked,s.path[j]);
  buckets[s.path.back()].push_back(std::move(s));
 }
 int L,R;long long placements=0,zero=0;int best=0;
 while(donorfile>>L>>R){
  Path l(L),r(R);for(auto&x:l)donorfile>>x;for(auto&x:r)donorfile>>x;
  array<int,8> perm;iota(perm.begin(),perm.end(),0);
  do{
   int mapv[256]{};for(int z=1;z<256;z++)mapv[z]=mapv[z&(z-1)]^1<<perm[countr_zero(unsigned(z))];
   auto& candidates=buckets[mapv[r[0]]];if(candidates.empty())continue;
   Mask ext{};for(int x:l)add(ext,mapv[x]);for(int x:r)add(ext,mapv[x]);
   placements+=candidates.size();
   for(auto&s:candidates){
    int defects=0;
    for(int k=0;k<4;k++){defects+=popcount(ext[k]&s.blocked[k]);if(defects>s.score)break;}
    if(defects>s.score)continue;
    int n=(L+R)+int(s.w.size());
    if(defects==s.score&&(defects>0&&n<=int(s.best.size())-1))continue;
    Path full;full.reserve(201);
    for(auto v=l.rbegin();v!=l.rend();v++)full.push_back(256+mapv[*v]);
    full.insert(full.end(),s.path.begin(),s.path.end());for(int v:r)full.push_back(256+mapv[v]);
    assert(int(full.size())==n+1);
    if(!defects){
     assert(valid(full));zero++;best=max(best,n);
     if(lengthen(full,192)){assert(valid(full));cout<<"FOUND "<<full.size()-1<<" "<<s.w;for(int v:full)cout<<" "<<v;cout<<endl;return 0;}
    }
    if(defects<s.score||n>int(s.best.size())-1){s.score=defects;s.best=std::move(full);}
   }
  }while(next_permutation(perm.begin(),perm.end()));
 }
 map<int,int> hist;
 for(const auto&group:buckets)for(const auto&s:group){hist[s.score]++;nearfile<<s.score<<" "<<s.w;for(int v:s.best)nearfile<<" "<<v;nearfile<<'\n';}
 cout<<"placements "<<placements<<" clean "<<zero<<" best_clean_edges "<<best<<" histogram";for(auto [d,n]:hist)cout<<" "<<d<<":"<<n;cout<<endl;
}
