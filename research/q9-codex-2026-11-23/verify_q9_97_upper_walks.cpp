// Enumerate the eight possible next coordinates of a rooted Q8 induced path.
// Independent of the original binary vertex-occupancy search.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
struct Pattern{int on,score;};
struct Factor{int yes=0,no=0,top=0;vector<Pattern> patterns;};
struct Change{int index,oldtop,mask;bool present;};
struct Walk{
 array<int,256> state{};array<vector<pair<int,int>>,256> refs;
 vector<Factor> factors;vector<Change> undo;vector<int> changed,path;
 long long bound,budget,nodes=0;int scale,need,root;bool limited=false;
 bool assign(int v,int sign){
  if(state[v])return state[v]==sign;
  state[v]=sign;changed.push_back(v);
  for(auto [idx,mask]:refs[v]){
   auto &f=factors[idx];bool present=sign>0;
   undo.push_back({idx,f.top,mask,present});
   if(present)f.yes|=mask;else f.no|=mask;
   int old=f.patterns[f.top].score;
   while(f.top<(int)f.patterns.size()){
    auto pick=f.patterns[f.top].on;
    if((pick&f.yes)==f.yes&&!(pick&f.no))break;
    ++f.top;
   }
   if(f.top==(int)f.patterns.size())return false;
   bound+=f.patterns[f.top].score-old;if(bound<(long long)need*scale)return false;
  }
  return true;
 }
 bool dfs(){
  if(++nodes>budget){limited=true;return false;}
  if((int)path.size()>=need)return true;
  int v=path.back(),prev=path.size()>=2?path[path.size()-2]:-1;
  for(int axis=0;axis<8;++axis){
   int next=v^(1<<axis);
   if(state[next])continue;
   auto u=undo.size(),c=changed.size();long long b=bound;
   bool pass=assign(next,1);
   for(int other=0;pass&&other<8;++other){
    int y=v^(1<<other);
    if(y!=next&&y!=prev)pass=assign(y,-1);
   }
   if(pass){path.push_back(next);if(dfs())return true;path.pop_back();}
   while(undo.size()>u){auto [idx,oldtop,mask,yes]=undo.back();undo.pop_back();auto& f=factors[idx];(yes?f.yes:f.no)&=~mask;f.top=oldtop;}
   while(changed.size()>c){state[changed.back()]=0;changed.pop_back();}
   bound=b;
   if(limited)return false;
  }return false;
 }
 bool read(){int count,n;long long original;
  if(!(cin>>root>>need>>scale>>bound>>original>>n))return false;
  state.fill(-1);for(int i=0,v;i<n;i++){cin>>v;state[v]=0;}
  cin>>count;factors.resize(count);
  for(int i=0;i<count;++i){
   auto &f=factors[i];int m;cin>>m;for(int j=0,v;j<m;++j){cin>>v;refs[v].push_back({i,1<<j});}
   cin>>m;f.patterns.resize(m);for(auto &p:f.patterns)cin>>p.on>>p.score;
   sort(f.patterns.begin(),f.patterns.end(),[](auto p,auto q){return p.score>q.score;});
   if(m==0)abort();bound+=f.patterns[0].score;
  }
  if(!cin||bound!=original)abort();return true;
 }
};
int main(int argc,char**argv){
 Walk w;if(!w.read())return 2;w.budget=argc>1?stoll(argv[1]):1000000000LL;
 w.path={w.root};bool found=w.assign(w.root,1)&&w.dfs();
 cout<<(found?"FOUND":w.limited?"UNKNOWN":"EXHAUSTED")<<' '<<w.nodes;
 if(found)for(int v:w.path)cout<<' '<<v;
 cout<<endl;
}
