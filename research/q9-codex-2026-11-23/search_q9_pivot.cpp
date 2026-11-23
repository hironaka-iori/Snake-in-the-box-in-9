// Inputs: rows of 192 nine-bit vertices, formatted as space-separated integers.
#include <array>
#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
using Count=uint64_t;
struct Pivot {
  array<bool,512> bad{};
  array<int,9> axes{}; array<vector<int>,9> ready;
  array<int,512> mapped{};
  array<int,10> fact{1,1,2,6,24,120,720,5040,40320,362880};
  Count leaves=0, nodes=0;
  bool visit(int level,int free) {
    ++nodes;
    if(level==9){++leaves;return true;}
    int axis=1<<axes[level];
    bool success=false;
    for(int x=free;x;x&=x-1){
      int image=x&-x;
      // Map all submasks newly determined by this assignment.
      int prior=0; for(int i=0;i<level;i++)prior|=1<<axes[i];
      for(int m=prior;;m=(m-1)&prior){mapped[m|axis]=mapped[m]|image;if(!m)break;}
      bool ok=true;
      for(int v:ready[level])if(bad[mapped[v]]){ok=false;break;}
      if(!ok){leaves+=fact[8-level];continue;}
      if(visit(level+1,free^image)){success=true;break;}
    }
    return success;
  }
  bool solve(const vector<int>&p,int cut){
    int c=p[cut];
    for(int i=0;i<=cut;i++){int u=p[i]^c;bad[u]=true;if(i<cut)for(int j=0;j<9;j++)bad[u^(1<<j)]=true;}
    vector<int> rel;for(size_t i=cut+1;i<p.size();i++)rel.push_back(p[i]^c);
    int assigned=0;
    for(int depth=0;depth<9;depth++){
      int high=-1,best=-1;
      for(int j=0;j<9;j++)if(!(assigned&(1<<j))){
        int score=0,avail=assigned|(1<<j);
        for(int v:rel)if((v&~avail)==0)++score;
        if(score>high){high=score;best=j;}
      }
      axes[depth]=best;assigned|=1<<best;
      for(int v:rel)if((v&~assigned)==0&&(v&(1<<best)))ready[depth].push_back(v);
    }
    return visit(0,511);
  }
};
bool valid(const vector<int>&p){
  for(size_t i=0;i<p.size();i++)for(size_t j=0;j<i;j++)
    if(p[i]==p[j] || ((popcount(unsigned(p[i]^p[j]))==1)!=(i==j+1)))return false;
  return true;
}
int main(int argc,char**argv){
  vector<int>b(192);Count seeds=0,cuts=0,perms=0,nodes=0;
  while(cin>>b[0]){
    for(int i=1;i<192;i++)if(!(cin>>b[i]))return 3;
    if(!valid(b))return 4;
    if(argc>1){Pivot t;if(!t.solve(b,95))return 5;cout<<"positive control passed\n";return 0;}
    for(int ori=0;ori<2;ori++,reverse(b.begin(),b.end())){
      for(int j=0;j<9;j++){
        int v=b.back()^(1<<j);if(find(b.begin(),b.end(),v)!=b.end())continue;
        vector<int>hits;for(int i=0;i<191;i++)if(popcount(unsigned(v^b[i]))==1)hits.push_back(i);
        if(hits.size()!=1)continue;
        ++seeds;vector<int>p=b;p.push_back(v);
        for(int k=hits[0]+1;k<192;k++){
          Pivot t;++cuts;
          if(t.solve(p,k)){
            auto w=p;for(int i=k+1;i<193;i++)w[i]=p[k]^t.mapped[p[i]^p[k]];
            if(!valid(w))return 6;cout<<"FOUND ";for(int x:w)cout<<x<<" ";cout<<"\n";return 0;
          }
          if(t.leaves!=362880)return 7;perms+=t.leaves;nodes+=t.nodes;
        }
      }
    }
  }
  cout<<"seeds "<<seeds<<" cuts "<<cuts<<" permutations "<<perms<<" nodes "<<nodes<<"\n";
}
