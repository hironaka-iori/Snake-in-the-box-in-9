// Re-embed a whole suffix, then regrow both ends in all nine dimensions.
#define main unused_pivot_main
#include "../search_q9_pivot.cpp"
#undef main
#include <cassert>
#include <cstdlib>
#include <functional>
#include <set>
#include <string>
using Path=vector<int>;
string key(const Path&p){
 string best;
 for(int s:{1,-1}){array<int,9> d;d.fill(-1);int n=0;string w;
 for(int j=1;j<p.size();j++){int i=s==1?j:p.size()-j;int a=countr_zero(unsigned(p[i]^p[i-1]));if(d[a]<0)d[a]=n++;w+=char('0'+d[a]);}if(best.empty()||w<best)best=w;
 }return best;
}
struct Extend{
 set<string> known, embedded;int best=0,radius=0;
 uint64_t goals=0,geometries=0,nodes=0,holds=0,perms=0;
 bool extend(Path&q,bool left=true){
  nodes++;int l=q.size()-1;
  if(l>=188&&l>=best){
   string word=key(q);if(known.insert(word).second){assert(valid(q));cout<<"WITNESS "<<l<<" "<<word;for(int v:q)cout<<" "<<v;cout<<endl;best=max(best,l);}
  }
  if(l>=192)return true;
  // End extensions commute. Grow on the left first, then only on the right.
  if(left && extend(q,false))return true;
  for(int i=0;i<9;i++){
   int v=(left?q.front():q.back())^(1<<i);bool ok=true;
   for(int j=left?1:0;j<int(q.size())-(left?0:1);j++)
    if(popcount(unsigned(q[j]^v))<=1){ok=false;break;}
   if(ok){
    if(left)q.insert(q.begin(),v);else q.push_back(v);
    if(extend(q,left))return true;
    if(left)q.erase(q.begin());else q.pop_back();
   }
  }
  return false;
 }
 bool placed(Path&p){
  geometries++;if(!embedded.insert(key(p)).second)return false;
  for(int total=0;total<=radius;total++)for(int a=0;a<=total;a++){
   Path q(p.begin()+a,p.end()-(total-a));
   if(extend(q))return true;
  }
  return false;
 }
 bool run(const Path&p,int cut){
  Pivot t;for(int i=0;i<=cut;i++){int v=p[i]^p[cut];t.bad[v]=true;if(i<cut)for(int d=0;d<9;d++)t.bad[v^(1<<d)]=true;}
  Path rel;for(int j=cut+1;j<p.size();j++)rel.push_back(p[j]^p[cut]);
  int assigned=0;array<int,9>prior{};for(int depth=0;depth<9;depth++){int bestscore=-1,axis=-1;prior[depth]=assigned;
   for(int j=0;j<9;j++)if(!(assigned>>j&1)){int s=0;for(int x:rel)s+=!(x&~(assigned|(1<<j)));if(s>bestscore){bestscore=s;axis=j;}}
   assigned|=1<<axis;t.axes[depth]=axis;for(int x:rel)if(!(x&~assigned)&&(x>>axis&1))t.ready[depth].push_back(x);
  }
  auto search=[&](auto&&self,int n,int avail)->bool{
   if(n==9){perms++;Path q(p.begin(),p.begin()+cut+1);for(int x:rel)q.push_back(p[cut]^t.mapped[x]);return placed(q);}
   int d=1<<t.axes[n];for(int opts=avail;opts;opts&=opts-1){int image=opts&-opts;
    for(int s=prior[n];;s=(s-1)&prior[n]){t.mapped[s|d]=t.mapped[s]|image;if(s==0)break;}
    bool ok=true;for(int x:t.ready[n])if(t.bad[t.mapped[x]]){ok=false;break;}
    if(!ok){perms+=t.fact[8-n];continue;}if(self(self,n+1,avail^image))return true;
   }return false;
  };
  holds++;return search(search,0,511);
 }
};
int main(int argc,char**argv){
 Extend solver;solver.radius=stoi(argv[1]);int stride=stoi(argv[2]);string word;
 while(cin>>word){Path p{0};for(char c:word)p.push_back(p.back()^(1<<(c-'0')));assert(valid(p));
  for(int i=24;i+24<p.size();i+=stride)if(solver.run(p,i))return 0;
 }
 assert(solver.perms==solver.holds*362880);
 cout<<"DONE pivots "<<solver.holds<<" permutations "<<solver.perms<<" valid_embeddings "<<solver.geometries<<" distinct_embeddings "<<solver.embedded.size()<<" end_search_nodes "<<solver.nodes<<" best_new "<<solver.best<<endl;
}
