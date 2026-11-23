#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Segment{int l,r;array<string,3> tracks;};
struct Search{
 string word,g,answer,built[2];vector<int> p;vector<Segment>s;array<int,512>occ{},nc{};mt19937 rng;int budget,local=0;
 long long nodes=0,pools=0,invalid=0,caps=0,fullFirst=0;
 Search(int limit,int seed):rng(seed),budget(limit){}
 void mark(int x,int k){occ[x]+=k;for(int j=0;j<9;j++)nc[x^1<<j]+=k;}
 bool dfs(int j,int u,int t,array<int,3>& ix){
    if(local>=budget)return false;++local;++nodes;auto&b=s[j];
    array<int,3> seq{0,1,2};shuffle(seq.begin(),seq.end(),rng);
    for(int k:seq)if(ix[k]<(int)b.tracks[k].size()){
       char c=b.tracks[k][ix[k]];int x=u^1<<(c-'0');bool last=t+1==b.r;
       if(last){if(x!=p[b.r])continue;}else{if(occ[x])continue;
          int needed=(t==b.l?1:1)+(t+2==b.r);
          if(nc[x]!=needed)continue;
       }
       ix[k]++;built[j]+=c;if(!last)mark(x,1);
       bool ok=false;if(!last)ok=dfs(j,x,t+1,ix);
       else if(j+1<(int)s.size()){++fullFirst;array<int,3>newix{};ok=dfs(j+1,p[s[j+1].l],s[j+1].l,newix);}
       else{answer=word;for(int id=0;id<(int)s.size();id++)answer.replace(s[id].l,s[id].r-s[id].l,built[id]);ok=true;}
       if(!last)mark(x,-1);built[j].pop_back();ix[k]--;if(ok)return true;if(local>=budget)break;
    }
    return false;
 }
 bool run(vector<pair<int,int>> changes){
    sort(changes.begin(),changes.end());vector<pair<int,int>> merged;
    for(auto [l,r]:changes){if(r-l<2)continue;if(merged.empty()||l>merged.back().second)merged.push_back({l,r});else merged.back().second=max(r,merged.back().second);}
    if(merged.empty())return false;
    s.clear();for(auto [l,r]:merged){Segment b;b.l=l;b.r=r;for(int t=l;t<r;t++)b.tracks[g[word[t]-'0']-'0']+=word[t];s.push_back(b);}
    if(s.size()==2&&rng()%2)swap(s[0],s[1]);occ.fill(0);nc.fill(0);array<int,512>at;at.fill(-10000);
    for(int i=0;i<(int)p.size();i++){bool free=false;for(auto&b:s)if(b.l<i&&i<b.r)free=true;if(free)continue;
       int x=p[i];if(occ[x]){++invalid;return false;}for(int d=0;d<9;d++)if(at[x^1<<d]>=0&&at[x^1<<d]!=i-1){++invalid;return false;}
       mark(x,1);at[x]=i;
    }
    ++pools;local=0;array<int,3>ix{};bool found=dfs(0,p[s[0].l],s[0].l,ix);caps+=local>=budget;return found;
 }
};
int main(int argc,char**argv){
 if(argc!=7)return 2;ifstream in(argv[1]);ofstream out(argv[2]);int tests=stoi(argv[3]),budget=stoi(argv[4]),seed=stoi(argv[5]),take=stoi(argv[6]);Search h(budget,seed);int row=0;long long trials=0;string w,g;
 while(row<take&&in>>w>>g){h.word=w;h.g=g;int n=w.size();h.p={0};for(char d:w)h.p.push_back(h.p.back()^1<<(d-'0'));vector<pair<int,int>>bad;for(int j=2;j<=n;j++)for(int i=0;i<j-1;i++)if(popcount((unsigned)(h.p[i]^h.p[j]))<=1)bad.emplace_back(i,j);
   if(bad.empty()){out<<row<<" 0 "<<w<<endl;++row;continue;}
   bool hit=false;for(int z=0;z<tests;z++){auto [a,b]=bad[h.rng()%bad.size()];int r=5+h.rng()%30;
     vector<pair<int,int>> blocks;for(int x:{a,b})if(0<x&&x<n){int l=max(0,x-1-int(h.rng()%r)),rr=min(n,x+1+int(h.rng()%r));blocks.emplace_back(l,rr);}
     if(blocks.size()==1&&h.rng()%2){int c=1+h.rng()%(n-1);blocks.emplace_back(max(0,c-r/2),min(n,c+r/2));}
     ++trials;if(h.run(blocks)){hit=true;out<<row<<' '<<z+1<<' '<<h.answer<<endl;break;}}
   ++row;if(hit&&n>=192)break;
 }
 cout<<"rows "<<row<<" windows "<<trials<<" compatible_exterior "<<h.pools<<" conflicting_exterior "<<h.invalid<<" nodes "<<h.nodes<<" first_routes "<<h.fullFirst<<" capped "<<h.caps<<endl;
}
