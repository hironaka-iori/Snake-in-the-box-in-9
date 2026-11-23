// Reuse the project's exact relative coordinate permutation checker.
#define main prior_pivot_main
#include "../search_q9_pivot.cpp"
#undef main
#include <fstream>
#include <string>
using Path=vector<int>;
vector<Path> read(const char*name){
 ifstream in(name);string w;vector<Path> arms;
 while(in>>w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));if(!valid(p))throw 1;arms.push_back(p);}
 return arms;
}
int main(int argc,char**argv){
 auto a=read(argv[1]);auto b=read(argv[2]);int lo=stoi(argv[3]),hi=min(stoi(argv[4]),(int)a.size());Count count=0,perms=0,nodes=0;
 bool symmetric=string(argv[1])==argv[2];
 for(int i=lo;i<hi;i++)for(int j=symmetric?i:0;j<b.size();j++){
  Path p(a[i].rbegin(),a[i].rend());int c=p.size()-1;p.insert(p.end(),b[j].begin()+1,b[j].end());Pivot t;
  if(t.solve(p,c)){for(int k=c+1;k<p.size();k++)p[k]=t.mapped[p[k]];if(!valid(p))return 1;
   cout<<"FOUND "<<p.size()-1<<" "<<i<<" "<<j;for(int v:p)cout<<" "<<v;cout<<endl;return 0;}
  if(t.leaves!=362880)return 2;count++;perms+=t.leaves;nodes+=t.nodes;
 }
 cout<<"COMPLETE A "<<lo<<" "<<hi<<" B "<<b.size()<<" pairs "<<count<<" placements "<<perms<<" nodes "<<nodes<<endl;
}
