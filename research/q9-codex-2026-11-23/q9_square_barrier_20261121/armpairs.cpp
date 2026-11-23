#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using Mask=array<uint64_t,8>;
struct Arm{Mask points{},blocked{};int n=0;};
struct Path{
 array<int,512> near{},used{};
 vector<int> core;
 void add(int x,int v){used[x]+=v;for(int i=0;i<9;i++)near[x^(1<<i)]+=v;}
 void arms(int x,const Arm&a,vector<Arm>&out){
  out.push_back(a);
  for(int i=0;i<9;i++){
   int y=x^(1<<i);if(used[y]||near[y]!=1)continue;Arm b=a;b.n++;
   b.points[y/64]|=uint64_t(1)<<(y%64);b.blocked[y/64]|=uint64_t(1)<<(y%64);
   for(int k=0;k<9;k++){int z=y^(1<<k);b.blocked[z/64]|=uint64_t(1)<<(z%64);}
   add(y,1);arms(y,b,out);add(y,-1);
  }
 }
 int max_edges(const string&w){
  core={0};for(char c:w)core.push_back(core.back()^(1<<(c-'0')));for(int v:core)add(v,1);
  vector<Arm>l,r;Arm empty;arms(core.front(),empty,l);arms(core.back(),empty,r);
  auto desc=[](const Arm&a,const Arm&b){return a.n>b.n;};sort(l.begin(),l.end(),desc);sort(r.begin(),r.end(),desc);
  int best=0;
  for(auto&a:l){if(a.n+r.front().n<=best)break;for(auto&b:r){
   if(a.n+b.n<=best)break;bool valid=true;for(int i=0;i<8;i++)if(a.points[i]&b.blocked[i]){valid=false;break;}
   if(valid){best=a.n+b.n;break;}
  }}
  return int(w.size())+best;
 }
};
int main(int argc,char**argv){if(argc<4)return 2;int stride=stoi(argv[1]);string kind=argv[2];
 for(int f=3;f<argc;f++){ifstream in(argv[f]);if(!in)throw runtime_error("file");string line;int index=0,count=0,best=0;while(getline(in,line)){
  if(index++%stride!=0)continue;istringstream ss(line);string word,unused;ss>>unused>>word;Path p;int n=p.max_edges(word);best=max(best,n);count++;
  if(kind=="records"&&n<stoi(unused))throw runtime_error("missing witness length");
  if(n>=192)cout<<"HIT "<<n<<" "<<word<<endl;
 }
 cout<<argv[f]<<" rows "<<index<<" checked "<<count<<" max "<<best<<endl;
 }}
