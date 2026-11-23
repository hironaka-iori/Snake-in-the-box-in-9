#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using U=uint64_t;
struct Set {
  array<U,4> a{};
  void add(int v){a[v/64]|=U(1)<<(v%64);}
  void del(int v){a[v/64]&=~(U(1)<<(v%64));}
  bool has(int v)const{return (a[v/64]>>(v%64))&1;}
  bool operator==(const Set&o)const{return a==o.a;}
};
const U masks[]={0x5555555555555555ULL,0x3333333333333333ULL,0x0f0f0f0f0f0f0f0fULL,0x00ff00ff00ff00ffULL,0x0000ffff0000ffffULL,0x00000000ffffffffULL};
Set adjacent(const Set &s){
  Set r;
  for(int j=0;j<4;j++){
    U x=s.a[j], y=s.a[j^1]|s.a[j^2];
    for(int d=0;d<6;d++)y|=((x&masks[d])<<(1<<d))|((x>>(1<<d))&masks[d]);
    r.a[j]=y;
  }
  return r;
}
Set parity;
array<Set,256> nbr;
struct Node{Set avail;array<unsigned char,257> path{};int depth=0;double score=0;};
int capacity(Node &s,int endpoint,int required){
  Set component;component.add(endpoint);
  for(;;){
    Set next=adjacent(component);
    for(int i=0;i<4;i++)next.a[i]=(next.a[i]&s.avail.a[i])|component.a[i];
    if(next==component)break;
    component=next;
  }
  s.avail=component;
  int n=0,even=0;
  for(int i=0;i<4;i++){
    n+=__builtin_popcountll(component.a[i]);
    even+=__builtin_popcountll(component.a[i]&parity.a[i]);
  }
  int same=__builtin_parity((unsigned)endpoint)?n-even:even;
  int bound=min(same*2,(n-same)*2+1);
  return bound<required?0:bound;
}
bool valid(const vector<int>&p){
  for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){
    int d=__builtin_popcount(unsigned(p[i]^p[j]));
    if(!d || (d==1)!=(j==i-1))return false;
  }
  return true;
}
int main(int argc,char**argv){
  if(argc!=4)return 2;
  int goal=stoi(argv[1]),width=stoi(argv[2]);
  mt19937_64 rng(stoul(argv[3]));
  for(int i=0;i<256;i++){
    if(!__builtin_parity((unsigned)i))parity.add(i);
    for(int b=0;b<8;b++)nbr[i].add(i^(1<<b));
  }
  string code;
  while(cin>>code){
    vector<int> lower{0};
    for(char d:code){if(d<'0'||d>'7')return 3;lower.push_back(lower.back()^(1<<(d-'0')));}
    if(!valid(lower))return 4;
    int target=goal-(int)lower.size();
    Node start;
    start.avail.a.fill(~U(0));
    for(int i=1;i<(int)lower.size();i++)start.avail.del(lower[i]);
    vector<Node> layer{start};
    bool clipped=false;long long expanded=0;int deepest=0;
    for(int depth=0;depth<target && !layer.empty();depth++){
      vector<Node> next;
      for(auto &state:layer){
        int tip=state.path[depth];
        for(int b=0;b<8;b++){
          int v=tip^(1<<b);
          if(!state.avail.has(v))continue;
          Node child=state;child.path[depth+1]=v;child.depth=depth+1;
          for(int i=0;i<4;i++)child.avail.a[i]&=~nbr[tip].a[i];
          child.avail.del(tip);child.avail.add(v);
          ++expanded;
          int cap=capacity(child,v,target-depth);
          if(!cap)continue;
          int options=0;
          for(int i=0;i<4;i++)options+=__builtin_popcountll(child.avail.a[i]&nbr[v].a[i]);
          child.score=cap+0.5*options+(rng()%1000000)/125000.;
          next.push_back(child);
        }
      }
      if(!next.empty())deepest=depth+1;
      if((int)next.size()>width){
        clipped=true;
        nth_element(next.begin(),next.begin()+width,next.end(),[](const Node&a,const Node&b){return a.score>b.score;});
        next.resize(width);
      }
      layer.swap(next);
    }
    if(deepest==target){
      auto full=lower;reverse(full.begin(),full.end());
      for(int i=0;i<=target;i++)full.push_back(256+layer.front().path[i]);
      if(!valid(full)||(int)full.size()!=goal+1)return 5;
      cout<<code<<" FOUND";for(int v:full)cout<<" "<<v;cout<<endl;
    }else cout<<code<<" "<<(clipped?"UNKNOWN":"EXHAUSTED")<<" "<<deepest<<" "<<expanded<<endl;
  }
}
