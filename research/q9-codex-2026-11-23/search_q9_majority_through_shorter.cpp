// Search the unordered majority-parity set. All 96 mediating vertices and
// the entire traversal order are free when the exact graph test runs.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <cmath>
#include <fstream>
#include <random>
#include <sstream>
#include <unordered_set>
using Path=vector<int>;
struct Fit {
 int value=0,cc=0,isolated=0,leaves=0,waste=0,edges=0,weak[128]{},nw=0;
 bool necessary=false;
};
struct Engine {
 mt19937_64 rng;
 int ri(int n){return rng()%n;}
 Engine(int seed):rng(seed){}
 Fit measure(Search &s){
  Fit t; int n=s.fixed.size();array<int,128> parent,sz{},deg{},supported{};int adj[128][10]{};
  for(int i=0;i<n;i++){parent[i]=i;sz[i]=1;}
  auto root=[&](int x){while(parent[x]!=x)x=parent[x];return x;};
  for(int v=0;v<512;v++){
   unsigned m=s.axes[v];if(popcount(m)!=2)continue;
   int a=s.slot[v^(1<<countr_zero(m))];m&=m-1;int b=s.slot[v^(1<<countr_zero(m))];
   bool duplicate=false;for(int k=0;k<deg[a];k++)if(adj[a][k]==b){duplicate=true;break;}if(duplicate)continue;
   adj[a][deg[a]++]=b;adj[b][deg[b]++]=a;t.edges++;
   int x=root(a),y=root(b);if(x!=y){if(sz[x]<sz[y])swap(x,y);parent[y]=x;sz[x]+=sz[y];}
  }
  int extra=0;for(int i=0;i<n;i++)if(deg[i]<=2)for(int j=0;j<deg[i];j++)supported[adj[i][j]]++;
  for(int i=0;i<n;i++){
   t.cc+=parent[i]==i;t.isolated+=deg[i]==0;t.leaves+=deg[i]==1;
   if(supported[i]>2)extra+=supported[i]-2;
   if(deg[i]<=1||supported[i]>=3)t.weak[t.nw++]=i;
  }
  t.waste=extra;t.necessary=t.cc==1&&t.isolated==0&&t.leaves<=2&&extra<=2&&t.edges>=n-1;
  t.value=7*(t.cc-1)+7*t.isolated+4*max(0,t.leaves-2)+3*max(0,extra-2)+2*max(0,n-1-t.edges);
  return t;
 }
 bool run(vector<Path> &bank,int chains,int steps){
  uint64_t proposals=0,eligible=0,tested=0,unknown=0,accepted=0;
  unordered_set<uint64_t> marked;array<uint64_t,512> rnd;for(auto &k:rnd)k=rng();
  int best=99999,furthest=0;uint64_t witnesses=0,extensions=0,extra_unknown=0;unordered_set<uint64_t> expanded;ofstream discard("/dev/null");
  for(int chain=0;chain<chains;chain++){
   Path initial=bank[ri(bank.size())];Search s(initial,2000,true);int n=initial.size();
   array<bool,512> orig{};for(int x:initial)orig[x]=true;
   Fit f=measure(s);uint64_t hash=0;for(int x:initial)hash^=rnd[x];int moved=0;
   for(int step=0;step<steps;step++){
    if(f.value<best){best=f.value;cout<<"ENERGY "<<best<<" CC "<<f.cc<<" leaves "<<f.leaves<<" forced excess "<<f.waste<<endl;}
    if(f.necessary && marked.insert(hash).second){
      ++tested;furthest=max(furthest,moved);bool ok;
      auto *backup=cout.rdbuf(discard.rdbuf());ok=s.test();cout.rdbuf(backup);
      if(ok){
       witnesses++;Search h(s.fixed,9000,true);int last=h.fixed.size();h.fixed.push_back(-1);
       for(int y=0;y<512;y++){
        if(h.slot[y]>=0||popcount(unsigned(y^h.fixed[0]))%2)continue;
        int choices=0;for(int d=0;d<9;d++)choices+=popcount(unsigned(h.axes[y^(1<<d)]))==1;
        if(!choices)continue;
        if(!expanded.insert(hash^rnd[y]).second)continue;
        h.fixed[last]=y;h.toggle(y,last,true);++extensions;
        if(h.test())return true;h.toggle(y,last,false);
       }
       extra_unknown+=h.unknown;
      }
    }
    if(step && ri(16)==0){
     // A cube isometry on one face alters multiple separated vertices in one move.
     int a=ri(9),b=(a+1+ri(8))%9, mask=0;
     int count=1+ri(4);
     while(popcount((unsigned)mask)<count){int d=ri(9);if(d!=a&&d!=b)mask|=1<<d;}
     int pattern=ri(512)&mask, kind=ri(2), delta=(1<<a)|(1<<b);
     Path candidate=s.fixed;int changes=0;
     for(int &x:candidate)if((x&mask)==pattern&&(kind||((x>>a)^(x>>b))&1)){x^=delta;changes++;}
     if(!changes)continue;Search next(candidate,2000,true);auto g=measure(next);
     if(g.value<=f.value||generate_canonical<double,53>(rng)<exp((f.value-g.value)/(1.5+chain%7))){
       unknown+=s.unknown; s=move(next);f=g;hash=0;moved=0;
       for(int x:s.fixed){hash^=rnd[x];moved+=!orig[x];}accepted++;
     }continue;
    }
    int i=ri(n);
    if(f.nw&&ri(100)<68){int weak=f.weak[ri(f.nw)];if(ri(4)==0)i=weak;else{
     int x=s.fixed[weak],d=ri(9);for(int h=0;h<9;h++){int v=x^(1<<((d+h)%9));unsigned m=s.axes[v];
      if(popcount(m)!=3)continue;m^=1<<((d+h)%9);if(ri(2))m&=m-1;
      i=s.slot[v^(1<<countr_zero(m))];break;}
    }}
    int old=s.fixed[i];s.toggle(old,i,false);int y=-1;
    for(int tr=0;tr<10;tr++){
     int k=ri(100),a=ri(9),b=(a+1+ri(8))%9;
     int v=k<40?(old^(1<<a)^(1<<b)):k<75?(s.fixed[f.nw?f.weak[ri(f.nw)]:ri(n)]^(1<<a)^(1<<b)):ri(512);
     if(v==old||s.slot[v]>=0||popcount(unsigned(v^old))%2)continue;
     int poss=0;for(int h=0;h<9;h++)poss+=popcount(unsigned(s.axes[v^(1<<h)]))==1;
     if(poss>=2||(poss==1&&ri(3)==0)){y=v;break;}
    }
    ++proposals;
    if(y<0){s.toggle(old,i,true);continue;}
    s.fixed[i]=y;s.toggle(y,i,true);auto g=measure(s);
    if(g.necessary)eligible++;
    double t=.12+double(2+chain%9)*pow(1.-double(step%900)/900.,2);
    if(g.value<=f.value||generate_canonical<double,53>(rng)<exp((f.value-g.value)/t)){
     f=g;hash^=rnd[old]^rnd[y];moved+=int(orig[old])-int(orig[y]);accepted++;
    }else{s.toggle(y,i,false);s.fixed[i]=old;s.toggle(old,i,true);}
   }
   unknown+=s.unknown;
   if(chain%100==0)cout<<"RUN "<<chain<<" steps "<<proposals<<" eligible "<<eligible<<" exact unique "<<tested<<" unknown "<<unknown<<" valid short sets "<<witnesses<<" longer sets tested "<<extensions<<" longer unknown "<<extra_unknown<<" max exchanges "<<furthest<<endl;
  }
  cout<<"DONE "<<proposals<<" accepted "<<accepted<<" eligible "<<eligible<<" exact unique "<<tested<<" unknown "<<unknown<<" valid short sets "<<witnesses<<" longer sets tested "<<extensions<<" longer unknown "<<extra_unknown<<" max exchanges "<<furthest<<endl;return false;
 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;int edges=stoi(argv[1]);vector<Path> bank;string l;
 while(getline(cin,l)){istringstream f(l);int x;Path a;while(f>>x)a.push_back(x);if((int)a.size()!=edges+1)continue;
  Path b;array<bool,512> seen{};for(int i=0;i<(int)a.size();i+=2){x=a[i];if(x<0||x>=512||seen[x]||popcount(unsigned(x^a[0]))%2)return 3;seen[x]=true;b.push_back(x);}
  bank.push_back(b);
 }if(bank.empty())return 4;
 Engine e(stoi(argv[4]));e.run(bank,stoi(argv[2]),stoi(argv[3]));
}
