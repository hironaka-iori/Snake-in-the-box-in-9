#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
// Four coordinate transpositions on Q8, with Q9 central edge on coordinate 8.
using namespace std;
using Mask=bitset<256>;
int mate(int x){return ((x&85)<<1)|((x&170)>>1);}
int main(int argc,char**argv){
  if(argc!=3)return 2;
  mt19937 rng(stoul(argv[1]));
  int trials=stoi(argv[2]);
  array<vector<int>,256> nb;
  array<Mask,256> block;
  for(int x=0;x<256;x++){
    block[x].set(x);
    if(x && x==mate(x))continue;
    for(int y=0;y<256;y++)if((y==0||y!=mate(y))&&y!=x&&
       (__builtin_popcount(x^y)==1||y==mate(x))){
      nb[x].push_back(y);block[x].set(y);
    }
  }
  vector<array<unsigned char,256>> maps;
  array<int,4> index{0,1,2,3};
  do{
    for(int flips=0;flips<16;flips++){
      array<unsigned char,256> m{};
      for(int x=1;x<256;x++){
        int j=__builtin_ctz(x),axis=2*index[j/2]+((j%2)^((flips>>(j/2))&1));
        m[x]=m[x&(x-1)]^(1<<axis);
      }
      maps.push_back(m);
    }
  }while(next_permutation(index.begin(),index.end()));
  vector<vector<int>> pool;
  string row;
  int best=0;
  while(getline(cin,row)){
    istringstream s(row);
    vector<int> p;int v;
    while(s>>v)p.push_back(v);
    if(p.size()<2||p.front()!=0)return 3;
    for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)
      if(p[i]==p[j]||block[p[j]][p[i]]!=(i==j+1))return 4;
    best=max(best,(int)p.size());pool.push_back(p);
  }
  if(pool.empty())return 5;
  for(int i=0;i<trials;i++){
    auto p=pool[rng()%pool.size()];
    int k=rng()%(p.size()-1),pivot=p[k];
    auto &m=maps[rng()%maps.size()];
    int span=rng()%5; if(rng()%4==0)span=0;
    int remove=(rng()%4==0)?rng()%4:0;
    int last=k+remove;
    if(last+1>=p.size())continue;
    vector<int> child(p.begin(),p.begin()+k+1);
    Mask ban;
    for(int j=0;j<k;j++)ban|=block[p[j]];
    bool ok=true;
    for(int j=0;j<span;j++){
      int x=child.back();
      auto &opts=nb[x];int y=opts[rng()%opts.size()];
      if(ban[y]){ok=false;break;}
      child.push_back(y);ban|=block[x];
    }
    if(!ok)continue;
    int offset=m[p[last]]^child.back();
    if(mate(offset)!=offset)continue;
    for(int j=last+1;j<p.size();j++){
      int y=m[p[j]]^offset,x=child.back();
      if((y&&mate(y)==y)||ban[y]||y==x||!block[x][y]){ok=false;break;}
      child.push_back(y);ban|=block[x];
    }
    if(!ok||child==p)continue;
    if(child.size()+2<best)continue;
    if(child.size()>best){
      best=child.size();cout<<"HALF 4";for(int x:child)cout<<" "<<x;cout<<endl;
      if(2*best-1>=193)return 0;
    }
    if(pool.size()<1024)pool.push_back(move(child));
    else pool[rng()%pool.size()]=move(child);
  }
  cerr<<"best edges "<<2*best-1<<" trials "<<trials<<"\n";
}
