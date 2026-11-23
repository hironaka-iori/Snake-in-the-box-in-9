#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Piece{string word;vector<int> points;int id,start,rev;};
int main(int argc,char**argv){
 int n=atoi(argv[1]),count=atoi(argv[2]);mt19937 rng(51770+n);
 vector<string> fixed;string w;if(argc>3){ifstream in(argv[3]);while(in>>w)fixed.push_back(w);}vector<string> mothers;while(cin>>w)mothers.push_back(w);
 vector<array<unsigned char,256>> maps;vector<array<int,8>> perms;
 array<int,8> dims; iota(dims.begin(),dims.end(),0);
 do{perms.push_back(dims);array<unsigned char,256> a{};for(int v=1;v<256;v++)a[v]=a[v&(v-1)]^(1<<dims[__builtin_ctz(v)]);maps.push_back(a);}while(next_permutation(dims.begin(),dims.end()));
 auto sample=[&](int len){
  int id=rng()%mothers.size(),start=rng()%(mothers[id].size()-len+1),rev=rng()%2;
  auto w=mothers[id].substr(start,len);if(rev)reverse(w.begin(),w.end());
  vector<int> v{0};for(char c:w)v.push_back(v.back()^(1<<(c-'0')));
  return Piece{w,v,id,start,rev};};
 for(int job=0;job<count;job++){
  auto a=sample(n/2);auto b=sample(n-1-n/2);
  if(!fixed.empty()){
   int len=a.word.size();int j;do{j=rng()%fixed.size();}while((int)fixed[j].size()<len);
   auto w=fixed[j].substr(0,len);a=Piece{w,{0},j,0,0};for(char c:w)a.points.push_back(a.points.back()^(1<<(c-48)));
  }
  array<int,256> used{};for(int v:a.points)used[v]=1;
  shuffle(b.points.begin(),b.points.end(),rng);int best=15,idx=-1;
  for(int j=0;j<(int)maps.size();j++){
   auto &lut=maps[j];int overlap=0;for(int v:b.points){overlap+=used[lut[v]];if(overlap>=best)break;}
   if(overlap<best){best=overlap;idx=j;}
  }
  if(idx<0)continue;
  auto ds=perms[idx];string p=a.word;reverse(p.begin(),p.end());p+='8';
  for(char c:b.word)p+='0'+ds[c-'0'];
  cout<<best<<" "<<job<<" "<<a.id<<" "<<a.start<<" "<<a.rev<<" "<<b.id<<" "<<b.start<<" "<<b.rev<<" ";for(int x:ds)cout<<x;cout<<" "<<p<<"\n";
 }
}
