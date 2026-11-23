#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using Perm=array<int,9>;
using Path=vector<int>;
struct Solver {
 Path p; int a=-1,b=-1; array<int,512> pos; array<array<int,10>,512> nearby{}; array<int,512> count{};
 Solver(Path x):p(x) {
  pos.fill(-1);
  for(int i=0;i<(int)p.size();i++){assert(p[i]>=0&&p[i]<512&&pos[p[i]]<0);pos[p[i]]=i;}
  for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));
   if(j+1==i){assert(d==1);continue;}if(d==1){assert(a<0);a=j;b=i;}}
  assert(a>=0);
  for(int v=0;v<512;v++){if(pos[v]>=0)nearby[v][count[v]++]=pos[v];for(int k=0;k<9;k++){int j=pos[v^(1<<k)];if(j>=0)nearby[v][count[v]++]=j;}}
 }
 bool close(const Path &im,int shift,int from,int forbidden,Path &w)const {
  array<char,512> incl{};array<int,512> queue;int n=1;queue[0]=from;incl[from]=1;
  auto add=[&](int j){if(!incl[j]){incl[j]=1;queue[n++]=j;}};
  for(int t=0;t<n;t++){
   int i=queue[t],v=im[i]^shift;
   for(int j:{i-1,i+1})if(j>=0&&j<(int)p.size()&&!has_single_bit(unsigned(v^p[j])))add(j);
   for(int h=0;h<count[v];h++){int j=nearby[v][h];if(abs(i-j)>1)add(j);}
   if(incl[forbidden])return false;
  }
  w=p;for(int h=0;h<n;h++)w[queue[h]]=im[queue[h]]^shift;
  for(int i=0;i<(int)w.size();i++)for(int j=0;j<i;j++)assert(w[i]!=w[j]&&(has_single_bit(unsigned(w[i]^w[j]))==(i==j+1)));
  return true;
 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;int order=stoi(argv[1]),extra=stoi(argv[2]),rows=stoi(argv[3]);mt19937 rng(stoi(argv[4]));
 Perm base; iota(base.begin(),base.end(),0);vector<Perm> perms; Perm g=base;
 do{int moved=0;for(int k=0;k<9;k++)moved+=g[k]!=k;if(moved<=order)perms.push_back(g);}while(next_permutation(g.begin(),g.end()));
 for(int i=0;i<extra;i++){shuffle(g.begin(),g.end(),rng);perms.push_back(g);}
 sort(perms.begin(),perms.end());perms.erase(unique(perms.begin(),perms.end()),perms.end());
 uint64_t transforms=0,closures=0;int row=0;string line;
 while(row<rows&&getline(cin,line)){istringstream in(line);int v;Path p;while(in>>v)p.push_back(v);Solver s(p);
  for(const auto &m:perms){array<int,512> map{};for(int v=1;v<512;v++){int bit=countr_zero(unsigned(v));map[v]=map[v^(1<<bit)]^(1<<m[bit]);}
   Path im;for(int x:p)im.push_back(map[x]);
   // A nonconstant selection must cross at least one path edge. Mark precisely the translations that could retain such a crossing in either direction.
   array<bool,512> possible{};
   for(int i=1;i<(int)p.size();i++)for(int k=0;k<9;k++){possible[im[i-1]^p[i]^(1<<k)]=true;possible[im[i]^p[i-1]^(1<<k)]=true;}
   for(int sh=0;sh<512;sh++)if(possible[sh]){transforms++;for(int dir=0;dir<2;dir++){int a=dir?s.b:s.a,b=dir?s.a:s.b;
    if(popcount(unsigned(im[a]^sh^p[b]))<2)continue;closures++;Path w;if(!s.close(im,sh,a,b,w))continue;
    cout<<"FOUND row "<<row<<" shift "<<sh<<" perm ";for(int k:m)cout<<k;cout<<" vertices";for(int x:w)cout<<" "<<x;cout<<endl;return 0;}}
  }
  row++;
  if(row%100==0)cout<<"CHECK "<<row<<" cases "<<transforms<<" closures "<<closures<<endl;
 }
 cout<<"DONE rows "<<row<<" permutations "<<perms.size()<<" transform_grid "<<uint64_t(row)*perms.size()*512<<" passing_crossing_filter "<<transforms<<" closures "<<closures<<endl;
 return 0;
}
