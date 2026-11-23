// Reroute two disjoint intervals while keeping the remaining three pieces in order.
#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using Path=std::vector<int>;
bool valid(const Path &p){
 for(int i=0;i<(int)p.size();++i)for(int j=0;j<i;++j){
  unsigned d=p[i]^p[j];
  if(!d || (__builtin_popcount(d)==1)!=(i==j+1))return false;
 }return true;
}
struct Trial{
 const Path &p;
 std::array<int,4> ends;
 std::array<int,2> lengths;
 int limit;bool flip=false;int visits=0;
 std::array<int,512> touches{};
 std::array<bool,512> used{};
 Path patches[2],answer;
 void mark(int x,int sign){used[x]=sign>0;for(int d=0;d<9;++d)touches[x^(1<<d)]+=sign;}
 bool route(int part,int x,int remain){
  if(++visits>limit)return false;
  int dest=p[ends[part?3:(flip?2:1)]],dist=__builtin_popcount((unsigned)(x^dest));
  if(dist>remain||((dist^remain)&1))return false;
  if(dist==1){
   if(remain!=1)return false;
   if(!part)return route(1,p[ends[flip?1:2]],lengths[1]);
   answer.assign(p.begin(),p.begin()+ends[0]+1);
   answer.insert(answer.end(),patches[0].begin(),patches[0].end());
   Path middle(p.begin()+ends[1],p.begin()+ends[2]+1);
   if(flip)std::reverse(middle.begin(),middle.end());
   answer.insert(answer.end(),middle.begin(),middle.end());
   answer.insert(answer.end(),patches[1].begin(),patches[1].end());
   answer.insert(answer.end(),p.begin()+ends[3],p.end());
   if(!valid(answer))std::abort();
   return true;
  }
  for(int d=0;d<9;++d){int y=x^(1<<d);
   if(used[y]||touches[y]!=(remain==2?2:1))continue;
   if(remain==2 && __builtin_popcount((unsigned)(y^dest))!=1)continue;
   patches[part].push_back(y);mark(y,1);
   if(route(part,y,remain-1))return true;
   mark(y,-1);patches[part].pop_back();if(visits>limit)return false;
  }
  return false;
 }
 bool run(){
  for(int i=0;i<(int)p.size();++i)
   if(!(ends[0]<i&&i<ends[1])&&!(ends[2]<i&&i<ends[3]))mark(p[i],1);
  return route(0,p[ends[0]],lengths[0]);
 }
};
int main(int argc,char **argv){
 if(argc<5||argc>6)return 2;
 bool reorder=argc==6 && std::string(argv[5])=="reorder";
 bool cross=argc==6 && !reorder;
 int target=std::stoi(argv[1]),runs=std::stoi(argv[2]),cap=std::stoi(argv[3]);std::mt19937 rng(std::stoul(argv[4]));
 std::vector<std::vector<std::pair<int,int>>> chords;std::vector<Path> bank;std::string line;
 while(std::getline(std::cin,line)){std::istringstream s(line);int v;Path p;while(s>>v){if(v<0||v>=512)return 3;p.push_back(v);}if(p.size()<100)return 3;
 std::vector<std::pair<int,int>> extra;
 for(int i=1;i<(int)p.size();++i)for(int j=0;j<i;++j){unsigned d=p[i]^p[j];if(!d||((j+1==i)&&__builtin_popcount(d)!=1))return 3;if(j+1<i&&__builtin_popcount(d)==1)extra.emplace_back(j,i);}
 chords.push_back(extra);bank.push_back(p);}
 if(bank.empty())return 3;
 long long nodes=0,capped=0,tries=0;
 for(int r=0;r<runs;++r){
  int idx=rng()%bank.size();const Path &p=bank[idx];int n=p.size()-1;
  int m=4+rng()%27,k=4+rng()%27,a=rng()%(n-m-k-2),b=a+m+1+rng()%(n-a-m-k);
  int delta=2*((int)(rng()%9)-4),req=target-n;
  auto cut=[&](int i){return (a<i&&i<a+m)||(b<i&&i<b+k);};
  bool clean=true;for(auto [u,v]:chords[idx])if(!cut(u)&&!cut(v))clean=false;
  if(!clean)continue;
  Path arranged;
  std::array<int,4> positions{a,a+m,b,b+k};
  if(reorder){
   std::array<Path,3> kept{Path(p.begin(),p.begin()+a+1),Path(p.begin()+a+m,p.begin()+b+1),Path(p.begin()+b+k,p.end())};
   std::shuffle(kept.begin(),kept.end(),rng);
   for(auto &block:kept)if(rng()%2)std::reverse(block.begin(),block.end());
   for(int j=0;j<3;++j){
    if(j)positions[j*2-1]=arranged.size();
    arranged.insert(arranged.end(),kept[j].begin(),kept[j].end());
    if(j<2){positions[j*2]=arranged.size()-1;arranged.resize(arranged.size()+(j?k:m)-1);}
   }
  }
  const Path &input=reorder?arranged:p;
  if((cross||reorder) && ((__builtin_popcount((unsigned)(input[positions[0]]^input[positions[cross?2:1]]))^(m+delta))&1))++delta;
  if(m+delta<2||k+req-delta<2)continue;
  Trial t{input,positions,{m+delta,k+req-delta},cap,cross};
  ++tries;bool ok=t.run();nodes+=t.visits;capped+=t.visits>cap;
  if(ok){if((int)t.answer.size()!=target+1)return 4;std::cout<<"FOUND";for(int x:t.answer)std::cout<<" "<<x;std::cout<<std::endl;return 0;}
 }
 std::cout<<"DONE target "<<target<<" donors "<<bank.size()<<" pairs_and_lengths "<<tries<<" capped "<<capped<<" nodes "<<nodes<<std::endl;
}
