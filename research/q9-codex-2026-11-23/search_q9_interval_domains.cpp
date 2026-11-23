// Partition a seed into short blocks bounded by fixed anchor vertices.
// Branch over all induced reroutings of each block, including both free tails.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using Mask=array<uint64_t,8>;
bool has(const Mask&a,int v){return a[v/64]>>(v%64)&1;}
void add(Mask&a,int v){a[v/64]|=1ULL<<(v%64);}
Mask combine(Mask a,const Mask&b){for(int j=0;j<8;j++)a[j]|=b[j];return a;}
struct Option { vector<int> v; Mask shadow{}; };
struct Block {int s,t;bool tail,rev;};
using Dom=vector<Option>;
using Index=vector<const Option*>;
struct Search{
  vector<int> p,anchors;
  vector<Block>b;
  vector<const Option*>chosen;
  int visits=0,cap=0;
  bool stopped=false;
  Mask halo[512]{};
  Search(){for(int v=0;v<512;v++){add(halo[v],v);for(int k=0;k<9;k++)add(halo[v],v^(1<<k));}}
  Dom generate(const Block& seg,int n){
    int u=p[seg.s],t=seg.tail?-1:p[seg.t]; Mask ban{};
    for(int a:anchors)if(p[a]!=u&&p[a]!=t)ban=combine(ban,halo[p[a]]);
    Dom out;vector<int>v;
    auto rec=[&](auto&&self,int x,int left,Mask blocked)->void{
      if(t>=0){
        int dist=popcount((unsigned)(x^t));
        if(((dist^left)&1) || dist>left || (dist!=left&&dist<=1))return;
        if(left==1){if(dist!=1)return;left=0;}
      }
      if(left==0){
        Option o;o.v=v;
        for(int y:v)o.shadow=combine(o.shadow,halo[y]);out.push_back(std::move(o));return;
      }
      auto next=combine(blocked,halo[x]);
      for(int j=0;j<9;j++){
        int y=x^(1<<j);
        if(y==t||has(blocked,y))continue;
        v.push_back(y);self(self,y,left-1,next);v.pop_back();
      }
    };
    rec(rec,u,n,ban);return out;
  }
  bool compatible(const Option&o,const Mask&ban){for(int v:o.v)if(has(ban,v))return false;return true;}
  bool solve(vector<Index> d,Mask ban,int todo){
    if(todo==0)return true;
    if(++visits>cap){stopped=true;return false;}
    int k=-1;
    for(int i=0;i<(int)b.size();i++)if(!chosen[i]){
      auto& dom=d[i];erase_if(dom,[&](const Option*o){return !compatible(*o,ban);});
      if(dom.empty())return false;
      if(k<0||dom.size()<d[k].size())k=i;
    }
    for(auto o:d[k]){
      chosen[k]=o;
      if(solve(d,combine(ban,o->shadow),todo-1))return true;
      chosen[k]=nullptr;
      if(stopped)return false;
    }
    return false;
  }
  // Variable lengths allow growth in two blocks to offset a shortening elsewhere.
  bool flexible(vector<Index> d,Mask ban,int remaining,int needed){
    if(!remaining)return needed==0;
    if(++visits>cap){stopped=true;return false;}
    int k=-1;
    vector<int> lo(b.size()),hi(b.size());
    bool changed=true;
    while(changed){
      changed=false;
      vector<Mask> f(b.size()),pref(b.size()+1),suff(b.size()+1);
      int total_lo=0,total_hi=0;
      for(int i=0;i<(int)b.size();i++)if(!chosen[i]){
        auto& dom=d[i];
        erase_if(dom,[&](const Option*o){return !compatible(*o,ban);});
        if(dom.empty())return false;
        lo[i]=512;hi[i]=0;f[i]=dom.front()->shadow;
        for(const auto* o:dom){
          int size=o->v.size();lo[i]=min(lo[i],size);hi[i]=max(hi[i],size);
          for(int word=0;word<8;word++)f[i][word]&=o->shadow[word];
        }
        total_lo+=lo[i];total_hi+=hi[i];
      }
      if(needed<total_lo||needed>total_hi)return false;
      for(int i=0;i<(int)b.size();i++)pref[i+1]=combine(pref[i],f[i]);
      for(int i=int(b.size())-1;i>=0;i--)suff[i]=combine(suff[i+1],f[i]);
      for(int i=0;i<(int)b.size();i++)if(!chosen[i]){
        auto& dom=d[i];auto required=combine(pref[i],suff[i+1]);auto old=dom.size();
        erase_if(dom,[&](const Option*o){int n=o->v.size();
          return n+total_lo-lo[i]>needed||n+total_hi-hi[i]<needed||!compatible(*o,required);});
        if(dom.empty())return false;
        changed|=dom.size()!=old;
      }
    }
    // Look for a change in length before branching on interchangeable same-length routes.
    int best=4;
    for(int i=0;i<(int)b.size();i++)if(!chosen[i]){
      int priority=lo[i]!=hi[i]?0:(d[i].size()>1?1:2);
      if(priority<best || (priority==best && d[i].size()<d[k].size())){k=i;best=priority;}
    }
    if(best==2){
      for(int i=0;i<(int)b.size();i++)if(!chosen[i])chosen[i]=d[i][0];
      return true;
    }
    stable_sort(d[k].begin(),d[k].end(),[](auto x,auto y){return x->v.size()>y->v.size();});
    for(auto o:d[k]){
      chosen[k]=o;
      if(flexible(d,combine(ban,o->shadow),remaining-1,needed-int(o->v.size())))return true;
      chosen[k]=nullptr;
      if(stopped)return false;
    }
    return false;
  }
  vector<int> path(){
    vector<int>q;
    for(int i=0;i<(int)b.size();i++){
      auto w=chosen[i]->v;if(b[i].rev)reverse(w.begin(),w.end());
      if(!b[i].rev)q.push_back(p[b[i].s]);q.insert(q.end(),w.begin(),w.end());
    }
    return q;
  }
  bool valid(const vector<int>&q){
    for(int i=0;i<(int)q.size();i++)for(int j=0;j<i;j++)
      if(q[i]==q[j] || ((popcount((unsigned)(q[i]^q[j]))==1)!=(i==j+1)))return false;
    return true;
  }
};
int main(int argc,char**argv){
  if(argc!=7 && argc!=8){cerr<<"bank partitions minspan maxspan nodecap rngseed [flex|reorder|positive-control|flex-control]\n";return 2;}
  ifstream file(argv[1]);string line;
  vector<vector<int>>bank;while(getline(file,line)){if(line.starts_with("n,"))continue;stringstream ss(line.substr(line.rfind(',')+1));vector<int>p;int x;while(ss>>x)p.push_back(x);if(p.size()!=191 && p.size()!=192)return 3;bank.push_back(p);}
  bool control=argc==8 && string(argv[7])=="positive-control";bool flex=argc==8 && string(argv[7])=="flex";bool reorder=argc==8 && string(argv[7])=="reorder";if(reorder)flex=true;bool flexcontrol=argc==8 && string(argv[7])=="flex-control";if(flexcontrol){control=true;flex=true;} Search h;int rounds=stoi(argv[2]),mn=stoi(argv[3]),mx=stoi(argv[4]);h.cap=stoi(argv[5]);mt19937 rng(stoi(argv[6]));shuffle(bank.begin(),bank.end(),rng);
  if(bank.empty() || (bank.front().size()==192 && !flex))return 3;
  long long cases=0,unknown=0,nodes=0;
  for(int r=0;r<rounds;r++){
    h.p=bank[r%bank.size()];if(control)h.p.resize(189);int target=control?191:193;int final_index=int(h.p.size())-1;if(!h.valid(h.p))return 4;h.anchors.clear();h.b.clear();
    int a=1+rng()%3,z=final_index-(1+rng()%3);h.anchors.push_back(a);
    while(a+mx<z){a+=mn+rng()%(mx-mn+1);h.anchors.push_back(a);}
    if(a!=z)h.anchors.push_back(z);
    vector<int> spans{h.anchors.front()};
    for(int i=1;i<(int)h.anchors.size();i++)spans.push_back(h.anchors[i]-h.anchors[i-1]);
    spans.push_back(final_index-z);
    if(reorder){
      vector<pair<int,int>> options;
      auto dist=[&](int i,int j){ return popcount((unsigned)(h.p[h.anchors[i]]^h.p[h.anchors[j]])); };
      for(int i=1;i+2<(int)h.anchors.size();i++)for(int j=i+1;j+1<(int)h.anchors.size();j++){
        if(((h.anchors[i]^h.anchors[j])&1)||spans[i]==1||spans[j+1]==1)continue;
        if(dist(i-1,j)<=spans[i]+2 && dist(i,j+1)<=spans[j+1]+2)options.emplace_back(i,j);
      }
      if(options.empty())continue;
      auto [i,j]=options[rng()%options.size()];
      reverse(h.anchors.begin()+i,h.anchors.begin()+j+1);
      reverse(spans.begin()+i+1,spans.begin()+j+1);
    }
    h.b.push_back({h.anchors[0],0,true,true});for(int i=1;i<(int)h.anchors.size();i++)h.b.push_back({h.anchors[i-1],h.anchors[i],false,false});
    h.b.push_back({z,final_index,true,false});
    vector<array<Dom,3>> ds(h.b.size());
    for(int i=0;i<(int)h.b.size();i++){
      auto g=h.b[i];int n=spans[i];
      ds[i][0]=h.generate(g,n);
      if(!reorder && ds[i][0].empty())return 5;
      if(g.tail)ds[i][1]=h.generate(g,n+1);
      ds[i][2]=h.generate(g,n+2);
    }
    if(flex){
      vector<vector<Dom>> added(h.b.size());
      vector<Index>d(h.b.size());
      for(int i=0;i<(int)h.b.size();i++){
        auto g=h.b[i];int n=spans[i];
        for(int delta=-2;delta<0;delta++){
          if(!g.tail&&delta==-1)continue;
          if(n+delta<(g.tail?0:1))continue;
          added[i].push_back(h.generate(g,n+delta));
        }
        for(auto &dom:ds[i])for(auto&o:dom)d[i].push_back(&o);
        for(auto &dom:added[i])for(auto&o:dom)d[i].push_back(&o);
      }
      h.chosen.assign(h.b.size(),nullptr);h.visits=0;h.stopped=false;cases++;
      if(h.flexible(std::move(d),{},h.b.size(),target-int(h.anchors.size()))){
        auto q=h.path();if(int(q.size())!=target||!h.valid(q))return 6;
        cout<<(control?"CONTROL":"FOUND");for(int v:q)cout<<" "<<v;cout<<endl;return 0;
      }
      unknown+=h.stopped;nodes+=h.visits;
    }else for(int k=-2;k<(int)h.b.size();k++){
      if(k==-1)continue;
      vector<Index> d(h.b.size());
      for(int i=0;i<(int)h.b.size();i++){
        auto& opts=ds[i][k==-2?(h.b[i].tail?1:0):(i==k?2:0)];
        for(auto&o:opts)d[i].push_back(&o);
      }
      h.chosen.assign(h.b.size(),nullptr);h.visits=0;h.stopped=false;cases++;
      if(h.solve(std::move(d),{},h.b.size())){
        auto q=h.path();if(int(q.size())!=target||!h.valid(q))return 6;
        cout<<(control?"CONTROL":"FOUND");for(int v:q)cout<<" "<<v;cout<<endl;return 0;
      }
      unknown+=h.stopped;nodes+=h.visits;
    }
    if(r==0||(r+1)%75==0||r+1==rounds)cout<<"partitions "<<r+1<<" cases "<<cases<<" unknown "<<unknown<<" nodes "<<nodes<<endl;
  }
}
