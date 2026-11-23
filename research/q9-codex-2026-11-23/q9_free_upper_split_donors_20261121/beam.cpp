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
#include <functional>
using P=vector<int>;
using Parts=vector<P>;
mt19937_64 gen(242738194);
long long tried,expanded;
P best;
int width;
void record(P p){
 if(p.size()<=best.size())return;
 if(!valid(p)){cerr<<"Invalid"<<endl;exit(8);}
 best=move(p);
}
void longbridge(P prefix,const P &last,Set avail,int s,int t){
 Node init;init.avail=avail;init.path[0]=s;vector<Node> layer{init};
 ++tried;
 for(int depth=0;depth<165 && !layer.empty();++depth){
   vector<Node> next;
   for(auto &a:layer){
    int u=a.path[depth];
    if(__builtin_popcount(unsigned(u^t))==1){
      if(prefix.size()+depth+2+last.size()>best.size()){
       P q=prefix;for(int j=0;j<=depth;++j)q.push_back(256+a.path[j]);q.push_back(256+t);q.insert(q.end(),last.begin(),last.end());record(move(q));
      }
      continue;
    }
    for(int k=0;k<8;++k){
     int v=u^(1<<k);if(!a.avail.has(v))continue;
     Node c=a;c.path[depth+1]=v;
     for(int j=0;j<4;++j)c.avail.a[j]&=~nbr[u].a[j];
     c.avail.del(u);c.avail.add(v);
     int threshold=max(1,(int)best.size()-(int)prefix.size()-(int)last.size()-depth);
     ++expanded;int cap=capacity(c,v,threshold);
     if(!cap || !c.avail.has(t))continue;
     int nd=0;for(int j=0;j<4;++j)nd+=__builtin_popcountll(c.avail.a[j]&nbr[v].a[j]);
     c.score=cap+nd*0.6+double(gen()%1000)/80.;
     next.push_back(c);
    }
   }
   if((int)next.size()>width){
    nth_element(next.begin(),next.begin()+width,next.end(),[](auto &x,auto &y){return x.score>y.score;});next.resize(width);
   }
   layer.swap(next);
 }
}
void routine(Parts parts,int maxRuns){
 int n=parts.size();P perm;for(int j=0;j<n;++j)perm.push_back(j);
 vector<Parts> orders;
 do{
  for(int m=0;m<(1<<n);++m){
   Parts v;for(int i=0;i<n;++i){v.push_back(parts[perm[i]]);if(m>>i&1)reverse(v.back().begin(),v.back().end());}
   orders.push_back(v);
  }
 }while(next_permutation(perm.begin(),perm.end()));
 shuffle(orders.begin(),orders.end(),gen);
 for(auto &g:orders){
  if(tried>=maxRuns)break;
  int s=g[n-2].back(),t=g.back().front();
  Set a;a.a.fill(~U(0));for(auto &island:g)for(int x:island)a.del(x);
  a.add(s);a.add(t);
  if(n==2){longbridge(g.front(),g.back(),a,s,t);continue;}
  int x=g[0].back(),e=g[1].front();a.add(e);a.add(x);
  P partial{x};int accepted=0;
  function<void(Set)> dfs=[&](Set open){
   int u=partial.back(),depth=partial.size()-1;
   if(accepted>=2 || depth+__builtin_popcount(unsigned(e^u))>min(10,__builtin_popcount(unsigned(e^x))+2))return;
   if(nbr[u].has(e)){
     P prefix=g[0];Set keep=a;
     for(int b:partial){prefix.push_back(b+256);keep.del(b);for(int j=0;j<4;++j)keep.a[j]&=~nbr[b].a[j];}
     prefix.push_back(e+256);keep.del(e);for(int j=0;j<4;++j)keep.a[j]&=~nbr[e].a[j];
     if(!keep.has(s)||!keep.has(t))return;
     prefix.insert(prefix.end(),g[1].begin(),g[1].end());++accepted;longbridge(prefix,g[2],keep,s,t);return;
   }
   P v;for(int k=0;k<8;++k){int z=u^(1<<k);if(open.has(z)&&z!=s&&z!=t)v.push_back(z);}
   shuffle(v.begin(),v.end(),gen);
   open.del(u);for(int j=0;j<4;++j)open.a[j]&=~nbr[u].a[j];
   for(int z:v){partial.push_back(z);Set opt=open;opt.add(z);dfs(opt);partial.pop_back();if(accepted>=2)break;}
  };dfs(a);
 }
}
int main(int argc,char**argv){
 width=stoi(argv[1]);int runs=stoi(argv[2]);for(int i=0;i<256;++i){if(!__builtin_parity((unsigned)i))parity.add(i);for(int k=0;k<8;++k)nbr[i].add(i^(1<<k));}
 int id,n;while(cin>>id>>n){Parts p(n);for(auto &q:p){int k;cin>>k;q.resize(k);for(int &x:q)cin>>x;}
 tried=expanded=0;best.clear();routine(p,runs);
 cout<<id<<" "<<tried<<" "<<expanded<<" "<<int(best.size())-1;for(int v:best)cout<<" "<<v;cout<<endl;
 }
}
