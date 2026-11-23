#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using Path=vector<int>;
int hd(int a,int b){return popcount(unsigned(a^b));}
bool valid(const Path&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||((hd(p[i],p[j])==1)!=(i==j+1)))return false;return true;}
struct Walk{
 Path p; array<unsigned char,512> used{},adj{};
 void put(int v){p.push_back(v);used[v]=1;for(int d=0;d<9;d++)adj[v^(1<<d)]++;}
 bool ok(int v){return !used[v]&&adj[v]==1;}
 void undo(){int v=p.back();p.pop_back();used[v]=0;for(int d=0;d<9;d++)adj[v^(1<<d)]--;}
};
struct Run{
 mt19937 rng;int goal,reps,depth,mode,best=0;long placements=0,trials=0;int row=0;Path bestp;
 vector<Path> comps;array<int,512> who{},pos{};Walk walk;
 Path next;int rank=-1;
 int get(int m){return rng()%m;}
 void save(){if(walk.p.size()<=best+1)return;best=walk.p.size()-1;bestp=walk.p;assert(valid(bestp));cout<<"BEST "<<best<<" row "<<row<<" vertices";for(int v:bestp)cout<<' '<<v;cout<<endl;}
 void choice(int orig,int bonus){int len=walk.p.size()-orig;if(!len)return;int score=25*len+get(mode?100:12)+bonus;if(score>rank){rank=score; next.assign(walk.p.begin()+orig,walk.p.end());}}
 void macro(const Path&s,int idx,int step,int shift,int orig,int bonus){
  int end=walk.p.size();placements++;for(int i=idx;i>=0&&i<s.size();i+=step){int v=s[i]^shift;if(!walk.ok(v))break;walk.put(v);}
  if(walk.p.size()>end+1)choice(orig,bonus);while(walk.p.size()>end)walk.undo();
 }
 void bridges(int orig,int left,int bridgecap){
  int tip=walk.p.back();for(int d=0;d<9;d++){int v=tip^(1<<d);if(!walk.ok(v))continue;
   if(who[v]>=0){for(int dir:{-1,1})macro(comps[who[v]],pos[v],dir,0,orig,40);}
   if(mode&&left==bridgecap){
    for(int i=0;i<11;i++){auto &s=comps[get(comps.size())];int dir=get(2)?1:-1;int k=dir==1?0:s.size()-1;if(i%3==0)k=get(s.size());macro(s,k,dir,s[k]^v,orig,0);}
   }
   walk.put(v);if(left>0)bridges(orig,left-1,bridgecap);else if(mode)choice(orig,-10);walk.undo();
  }
 }
 void sample(int rep){trials++;walk={};int j=get(comps.size());if(rep%4==0)j=max_element(comps.begin(),comps.end(),[](auto&a,auto&b){return a.size()<b.size();})-comps.begin();
  Path start=comps[j];if(get(2))reverse(start.begin(),start.end());for(int v:start)walk.put(v);
  int stale=0;for(int it=0;it<125&&stale<2;it++){save();if(best>=goal)return;rank=-1;next.clear();int n=walk.p.size();bridges(n,depth,depth);if(next.empty())stale++;else {for(int v:next)walk.put(v);stale=0;}
   if(stale||get(3)==0)reverse(walk.p.begin(),walk.p.end());}
  save();
 }
 void load(vector<Path> p){comps=move(p);who.fill(-1);for(int i=0;i<comps.size();i++)for(int j=0;j<comps[i].size();j++){who[comps[i][j]]=i;pos[comps[i][j]]=j;}}
};
int main(int argc,char**argv){if(argc<6)return 2;Run r;r.goal=atoi(argv[1]);r.reps=atoi(argv[2]);r.depth=atoi(argv[3]);r.mode=atoi(argv[4]);r.rng.seed(atoi(argv[5]));int nrows=0;string line;while(getline(cin,line)){stringstream in(line);int dim,nc,n,v;in>>dim>>nc>>n;vector<Path>p(1);while(in>>v){if(!p.back().empty()&&hd(v,p.back().back())!=1)p.emplace_back();p.back().push_back(v);}assert(nc==p.size());if(nc>=7){r.load(move(p));nrows++;for(int k=0;k<r.reps;k++){r.sample(k);if(r.best>=r.goal)break;}}if(r.best>=r.goal)break;r.row++;}
 cout<<"DONE sections "<<nrows<<" trials "<<r.trials<<" macro_placements "<<r.placements<<" best "<<r.best<<endl;
}
