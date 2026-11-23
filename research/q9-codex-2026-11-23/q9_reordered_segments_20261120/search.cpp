#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using P=vector<int>; using Mask=array<uint64_t,8>;
void mark(Mask&m,int x){m[x/64]|=1ULL<<(x%64);}
bool intersects(const Mask&a,const Mask&b){for(int i=0;i<8;i++)if(a[i]&b[i])return true;return false;}
int hd(int x,int y){return popcount(unsigned(x^y));}
int check(const P&p){int n=0;for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){int h=hd(p[i],p[j]);if(!h||(j+1==i&&h!=1))return -1;n+=(h==1&&j+1<i);}return n;}
string canon(const P&p){string best;for(int rev:{0,1}){array<int,9>r;r.fill(-1);string w;int n=0;for(int j=1;j<p.size();j++){int k=rev?p.size()-j:j;int b=countr_zero(unsigned(p[k]^p[k-1]));if(r[b]<0)r[b]=n++;w+=char('0'+r[b]);}if(best.empty()||w<best)best=w;}return best;}
struct Join{P v;Mask m{},ban{};};
struct Engine{
 int goal,depth,radius;mt19937 rng;uint64_t tried=0,orders=0,bridges=0,tuples=0,joined=0,tips=0,broken=0;int best=0;P answer;vector<P> seg;bool movable=false,guided=false;int caseid=-1;string cutting,orderlabel;set<string> high;array<int,512> fixed{},adj{};int kept=0;bool control;
 vector<Join> conn(int a,int b,int maxinner){
  vector<Join> res;array<int,512> hit{},taken{};P p;
  auto dfs=[&](auto&&self,int x)->void{
   for(int i=0;i<9;i++){int v=x^(1<<i);if(fixed[v]||taken[v]||hit[v]!=(int)!p.empty())continue;
    int other=adj[v]-(p.empty()?1:0);bool end=hd(v,b)==1;
    if(other!=(int)end)continue;
    p.push_back(v);
    if(end){Join j;j.v=p;for(int z:p){mark(j.m,z);mark(j.ban,z);for(int k=0;k<9;k++)mark(j.ban,z^(1<<k));}res.push_back(move(j));}
    else if((int)p.size()+hd(v,b)-1<=maxinner&&(int)p.size()<maxinner){
     for(int k=0;k<9;k++)hit[v^(1<<k)]++;taken[v]=1;self(self,v);taken[v]=0;for(int k=0;k<9;k++)hit[v^(1<<k)]--;
    }p.pop_back();
   }
  };if(hd(a,b)==1){res.emplace_back();return res;}if(maxinner>=1&&hd(a,b)<=maxinner+1)dfs(dfs,a);bridges+=res.size();return res;
 }
 bool extend(P&p,bool first=true){tips++;best=max(best,(int)p.size()-1);if(!control&&p.size()>=191){auto w=canon(p);if(high.insert(w).second){assert(check(p)==0);cout<<"VALID "<<p.size()-1<<" source "<<caseid<<" holes "<<cutting<<" order "<<orderlabel<<" vertices";for(int v:p)cout<<" "<<v;cout<<endl;}}if(p.size()==goal+1){assert(check(p)==0);answer=p;return true;}
  if(first&&extend(p,false))return true;
  for(int i=0;i<9;i++){int v=(first?p.front():p.back())^(1<<i);bool ok=true;for(int j=first?1:0;j<int(p.size())-(first?0:1);j++)if(hd(v,p[j])<=1){ok=false;break;}
   if(ok){if(first)p.insert(p.begin(),v);else p.push_back(v);if(extend(p,first))return true;if(first)p.erase(p.begin());else p.pop_back();}
  }return false;
 }
 bool search(vector<P> blocks){
  tried++;seg=move(blocks);kept=0;fixed.fill(0);adj.fill(0);for(auto&s:seg){kept+=s.size();for(int x:s){fixed[x]++;for(int k=0;k<9;k++)adj[x^(1<<k)]++;}}
  for(auto&s:seg)for(int i=0;i<s.size();i++)if(fixed[s[i]]!=1||adj[s[i]]!=1+(i>0&&i+1<s.size()))return false;
  int room=goal+1-kept,n=seg.size();if(room<0)return false;
  // Restrict to genuine reordering of two internal blocks. The original two terminal
  // blocks keep their positions, but every block may reverse independently.
  vector<int> ord(n);iota(ord.begin(),ord.end(),0);
  do{bool identity=true;for(int i=0;i<n;i++)identity &= ord[i]==i;if(identity)continue;
   if(movable&&(ord.front()>ord.back()||(ord.front()==0&&ord.back()==n-1)))continue;
   for(int flip=0;flip<(1<<n);flip++){
    array<int,6> a{},b{},lo{};int required=0;for(int i=0;i<n;i++){auto&s=seg[ord[i]];bool r=flip>>i&1;a[i]=r?s.back():s.front();b[i]=r?s.front():s.back();
      if(i){lo[i-1]=max(0,hd(b[i-1],a[i])-1);required+=lo[i-1];}}
    if(required>room)continue;orders++;
    array<vector<Join>,5> options;bool okay=true;
    for(int i=0;i<n-1;i++){int lim=min(depth,room-(required-lo[i]));options[i]=conn(b[i],a[i+1],lim);if(options[i].empty()){okay=false;break;}}
    if(!okay)continue;tuples++;vector<const Join*> chosen;
    auto choose=[&](auto&&self,int j,int used,Mask ban)->bool{
     if(j==n-1){if(room-used>radius)return false;P p;for(int i=0;i<n;i++){auto&s=seg[ord[i]];if(flip>>i&1)p.insert(p.end(),s.rbegin(),s.rend());else p.insert(p.end(),s.begin(),s.end());if(i<n-1)p.insert(p.end(),chosen[i]->v.begin(),chosen[i]->v.end());}
      joined++;assert(check(p)==0);orderlabel.clear();for(int k=0;k<n;k++)orderlabel+=to_string(ord[k])+(flip>>k&1?"-":"+");if(extend(p)){cout<<"ORDER";for(int z:ord)cout<<" "<<z;cout<<" FLIPS "<<flip<<" bridges";for(auto*z:chosen)cout<<" "<<z->v.size();cout<<endl;return true;}return false;}
     for(auto&q:options[j]){if(used+q.v.size()>room||intersects(q.m,ban))continue;Mask z=ban;for(int k=0;k<8;k++)z[k]|=q.ban[k];chosen.push_back(&q);if(self(self,j+1,used+q.v.size(),z))return true;chosen.pop_back();}return false;
    };if(choose(choose,0,0,{}))return true;
   }
  }while((movable?next_permutation(ord.begin(),ord.end()):next_permutation(ord.begin()+1,ord.end()-1)));return false;
 }
};
int main(int argc,char**argv){
 if(argc<6)return 2;Engine e;e.goal=stoi(argv[1]);e.control=stoi(argv[2]);int trials=stoi(argv[3]);e.depth=stoi(argv[4]);e.radius=stoi(argv[5]);e.rng.seed(argc>6?stoi(argv[6]):43158);e.movable=argc>7&&stoi(argv[7]);e.guided=argc>8&&stoi(argv[8]);string line;int row=0;vector<P>bank;vector<array<int,2>> chords;vector<vector<pair<int,int>>> old96;
 while(getline(cin,line)){P p;int x;istringstream in(line);while(in>>x)p.push_back(x);if(p.empty())continue;int c=check(p);if(c!=(e.control?0:1))continue;
  array<int,2> ij{};if(c)for(int i=0;i<p.size();i++)for(int j=0;j+1<i;j++)if(hd(p[i],p[j])==1)ij={j,i};
  bank.push_back(p);chords.push_back(ij);vector<pair<int,int>> win;
  if(!e.control)for(int i=0;i+96<p.size();i++){int mask=0;for(int j=i+1;j<=i+96;j++)mask|=p[j]^p[j-1];if(popcount(unsigned(mask))<9)win.emplace_back(i,i+96);}
  old96.push_back(win);
 }
 int attempts=0;
 for(int n=0;n<trials;n++){int id=n%bank.size();auto&p=bank[id];if(e.control&&n>10)break;vector<pair<int,int>> holes;
  int count=3+(!e.control&&(n+n/bank.size())%2==1);for(int i=0;i<count;i++){int w=e.control?(i%3)+1:1+e.rng()%(e.guided?8:5);int k=e.control?(p.size()*(i+1))/(count+1):((int)e.rng()%int(p.size()-14)+int(p.size()-14))%int(p.size()-14)+7;
   if(i==0&&!e.control){int idx=chords[id][(n/bank.size())%2];k=max(2,min((int)p.size()-w-2,idx-(int)(e.rng()%w)));}
   if(e.guided&&i>0){int low=100000;
    for(int rep=0;rep<13;rep++){int loc=6+e.rng()%(p.size()-w-12);int cost=100;
     for(auto[u,v]:holes){if(loc+w+4>=u&&v+5>=loc){cost=1000;break;}
      for(int t:{loc-1,loc+w})for(int z:{u-1,v+1})cost=min(cost,hd(p[t],p[z]));}
     int score=4*cost+e.rng()%15;if(score<low){low=score;k=loc;}
    }
   }
   holes.emplace_back(k,k+w-1);}
  sort(holes.begin(),holes.end());bool okay=holes.front().first>=2&&holes.back().second+2<(int)p.size();for(int j=1;j<holes.size();j++)okay&=holes[j].first-holes[j-1].second>=3;if(!okay)continue;
  for(auto [l,r]:old96[id]){bool broken=false;for(auto [a,b]:holes)broken|=b>=l&&a<=r;if(!broken){okay=false;break;}}if(!okay)continue;
  vector<P> blocks;int start=0;for(auto [a,b]:holes){blocks.emplace_back(p.begin()+start,p.begin()+a);start=b+1;}blocks.emplace_back(p.begin()+start,p.end());
  if(e.control)swap(blocks[1],blocks[2]);attempts++;e.caseid=id;e.cutting.clear();for(auto[a,b]:holes)e.cutting+=to_string(a)+"-"+to_string(b)+",";
  if(e.search(blocks)){cout<<"FOUND "<<e.goal<<" source "<<id<<" holes";for(auto [a,b]:holes)cout<<" "<<a<<"-"<<b;cout<<" vertices";for(int v:e.answer)cout<<" "<<v;cout<<endl;break;}
 }
 cout<<"DONE input "<<bank.size()<<" proposed "<<trials<<" accepted "<<attempts<<" bounded_orders "<<e.orders<<" bridge_choices "<<e.bridges<<" orders_with_connectors "<<e.tuples<<" valid_reorders "<<e.joined<<" tip_nodes "<<e.tips<<" best "<<e.best<<endl;
}
