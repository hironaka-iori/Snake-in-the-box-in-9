#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <vector>
using namespace std;using U=uint32_t;
int pc(U z){return __builtin_popcount(z);}
struct F{U m,d0,d1,d2;int c;};
vector<F> bank;vector<int> rep;long long pairs=0,nonempty=0,withfour=0,sol=0,degsol=0,partial=0;
int maxdom=0;map<int,int> lengths;
int main(int argc,char**argv){
 if(argc!=3)return 2;
 bool defectA=string(argv[1])=="A";
 F f;map<U,int> index;
 while(cin>>f.m>>f.d0>>f.d1>>f.d2>>f.c){index[f.m]=bank.size();bank.push_back(f);}
 vector<bool> used(bank.size());
 for(int i=0;i<(int)bank.size();i++)if(!used[i]){
  rep.push_back(i);array<int,5> pi{0,1,2,3,4};
  do{int mapv[32]{};for(int v=1;v<32;v++)mapv[v]=mapv[v&(v-1)]^(1<<pi[__builtin_ctz(v)]);
   for(int t=0;t<32;t++){U m=0;for(U q=bank[i].m;q;q&=q-1)m|=1u<<(t^mapv[__builtin_ctz(q)]);used[index.at(m)]=true;}
  }while(next_permutation(pi.begin(),pi.end()));
 }
 int full=bank.size();ifstream smaller(argv[2]);if(!smaller)return 3;while(smaller>>f.m>>f.d0>>f.d1>>f.d2>>f.c)bank.push_back(f);
 cerr<<"orbits "<<rep.size()<<endl;
 for(int i:rep)for(int j=defectA?0:full;j<(defectA?full:(int)bank.size());j++){
  const F& l=bank[i];const F&r=bank[j];pairs++;
  U b0=~(l.m|r.m),b1=l.m^r.m,b2=l.m&r.m;
  U forbid=l.d2|r.d2;
  vector<pair<int,int>> dom;
  vector<pair<int,int>> domSmall;auto domain=[&](int k){
   const F& a=bank[k];
   if((a.m&forbid)||(a.d2&~b0)||(a.d1&b2)||(a.d0&b0))return;
   int deficit=pc((a.d1&b0)|(a.d0&b1));if(deficit<=2)(k<full?dom:domSmall).emplace_back(k,deficit);
  };for(int k=0;k<full;k++)domain(k);
  if(dom.empty())continue;nonempty++;maxdom=max(maxdom,(int)dom.size());
  if(defectA)for(int k=full;k<bank.size();k++)domain(k);
  U atB=l.m|r.m;
  U needTwo=(l.d0|r.d0);
  U needSome=(l.d1|l.d0|r.d1|r.d0);
  U limitOne=(l.d1|r.d1); // if shared, count must satisfy both bounds
  array<int,4> choice;
  auto dfs=[&](auto&&self,int layer,int first,U seen,U twice,int score)->bool{
   partial++;
   if(score>2)return false;
   if(layer==4){withfour++;
    int deficit=score + pc(l.d0&~twice)+pc(r.d0&~twice)+pc(l.d1&~seen)+pc(r.d1&~seen);
    if(((l.d0|r.d0)&~seen)||deficit!=2)return false;
    degsol++;
    array<U,6> occ;for(int a=0;a<4;a++)occ[a]=bank[choice[a]].m;occ[4]=l.m;occ[5]=r.m;
    vector<int> adj[192];int endpoint=-1;
    for(int a=0;a<6;a++)for(U q=occ[a];q;q&=q-1){int v=__builtin_ctz(q),z=32*a+v;
     for(int d=0;d<5;d++)if((occ[a]>>(v^(1<<d)))&1)adj[z].push_back(a*32+(v^(1<<d)));
     for(int b=0;b<6;b++)if((a<4)!=(b<4)&&((occ[b]>>v)&1))adj[z].push_back(32*b+v);
     assert(adj[z].size()==1||adj[z].size()==2);
     if(adj[z].size()==1)endpoint=z;
    }
    vector<int> path;int prev=-1;while(endpoint>=0){path.push_back(endpoint);int next=-1;for(int t:adj[endpoint])if(t!=prev){next=t;break;}prev=endpoint;endpoint=next;}
    lengths[path.size()]++;if(path.size()!=95)return false;
    sol++;cout<<"PATH";for(int t:path)cout<<" "<<t;cout<<endl;
    return false;
   }
   bool small=defectA&&layer==3;const auto& candidates=small?domSmall:dom;
   for(int t=small?0:first;t<(int)candidates.size();t++){
    auto [k,def]=candidates[t];U on=bank[k].m&atB;
    if(on&(twice|(seen&limitOne)))continue;choice[layer]=k;
    if(self(self,layer+1,t,seen|on,twice|(on&seen),score+def))return true;
   }return false;
  };
  dfs(dfs,0,0,0,0,0);
 }
 for(auto [n,count]:lengths)cerr<<"component "<<n<<" "<<count<<endl; cerr<<"pairs "<<pairs<<" nonempty "<<nonempty<<" maxdom "<<maxdom<<" partial "<<partial<<" four-valid-cap "<<withfour<<" degree-sol "<<degsol<<" connected "<<sol<<endl;
}
