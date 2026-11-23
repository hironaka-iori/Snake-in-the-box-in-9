// Grow two disjoint upper arms from the tips of a fixed lower Q8 path.
#define main legacy_single_tip_main
#include "search_q8_layer_beam.cpp"
#undef main
#include <algorithm>
#include <bit>
#include <fstream>
#include <unordered_set>
struct State{Set avail,picked;int tip[2]={},len[2]={};double quality=0;};
struct Seed{vector<int> mid,arm[2];};
int pop(const Set&s){int n=0;for(U z:s.a)n+=std::popcount(z);return n;}
vector<int> decode(const vector<int>&mid,const State&s){
 vector<int>p;for(int side=0;side<2;side++){vector<int>r;int v=side?mid.back():mid.front(),prev=-1;
  for(;;){r.push_back(v+256);int next=-1;for(int d=0;d<8;d++){int z=v^1<<d;if(z==prev||!s.picked.has(z))continue;if(next!=-1)abort();next=z;}
   if(next<0)break;prev=v;v=next;}
  if(!side){p.assign(r.rbegin(),r.rend());p.insert(p.end(),mid.begin(),mid.end());}else p.insert(p.end(),r.begin(),r.end());
 }if(!valid(p))abort();return p;}
bool step(State&s,int side,int v){int x=s.tip[side],other=s.tip[1-side];if(!s.avail.has(v)||std::popcount((unsigned)(v^x))!=1||nbr[other].has(v))return false;
 s.picked.add(v);for(int j=0;j<4;j++)s.avail.a[j]&=~nbr[x].a[j];s.tip[side]=v;s.len[side]++;return true;}
U hashstate(const State&s){U h=s.tip[0]*311+s.tip[1];for(U x:s.picked.a){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;h=(h^x)*0x94d049bb133111ebULL;}return h;}
int evaluate(State&s,int need,int side,int required){
 Set front,reach;for(int arm=0;arm<2;arm++)for(int j=0;j<4;j++)front.a[j]|=nbr[s.tip[arm]].a[j]&s.avail.a[j]&~nbr[s.tip[1-arm]].a[j];
 reach=front;for(;;){Set n=adjacent(front);for(int j=0;j<4;j++){n.a[j]&=s.avail.a[j]&~reach.a[j];reach.a[j]|=n.a[j];}if(!pop(n))break;front=n;}
 s.avail=reach;int total=pop(reach);if(total<need)return -1;
 int colors[2]={};for(int j=0;j<4;j++)colors[0]+=std::popcount(reach.a[j]&parity.a[j]);colors[1]=total-colors[0];
 int demand[2]={};for(int arm=0;arm<2;arm++){int count=arm==side?required:need-required;int c=std::popcount((unsigned)s.tip[arm])%2;demand[1-c]+=(count+1)/2;demand[c]+=count/2;}
 if(colors[0]<demand[0]||colors[1]<demand[1])return -1;return total;
}
int main(int argc,char**argv){
 if(argc!=6)return 2;int goal=stoi(argv[1]),width=stoi(argv[2]),rounds=stoi(argv[3]);mt19937_64 rng(stoul(argv[4]));int warm=stoi(argv[5]);
 for(int i=0;i<256;i++){if(!(__builtin_parity((unsigned)i)))parity.add(i);for(int j=0;j<8;j++)nbr[i].add(i^1<<j);}
 vector<Seed> bank;string line;while(getline(cin,line)){istringstream in(line);Seed a;int n,x;if(!(in>>n))continue;for(int j=0;j<n;j++){in>>x;a.mid.push_back(x);}
  for(int i=0;i<2;i++){in>>n;for(int j=0;j<n;j++){in>>x;a.arm[i].push_back(x);}}if(!in||!valid(a.mid))abort();bank.push_back(a);}
 long long nodes=0,pruned=0;int best=0;
 for(int r=0;r<rounds;r++){const auto &b=bank[rng()%bank.size()];int need=goal+1-b.mid.size()-2;if(need<0)abort();State s;s.avail.a.fill(~U(0));for(int x:b.mid)s.avail.del(x);
  s.tip[0]=b.mid.front();s.tip[1]=b.mid.back();for(int x:s.tip)s.picked.add(x);
  int targetL=1+rng()%(need-1);if(!b.arm[0].empty()&&r%5!=0)targetL=std::clamp((int)b.arm[0].size()+(int)(rng()%19)-9,0,need);
  for(int i=0;i<2;i++){int share=i?need-targetL:targetL;int maxkeep=min(share,(int)b.arm[i].size());
   int keep=warm?max(0,maxkeep-(int)(rng()%(12+warm))):0;if(warm&&r%9==0)keep=maxkeep;
   for(int j=0;j<keep;j++)if(!step(s,i,b.arm[i][j]))break;}
  int start=s.len[0]+s.len[1];vector<State> active{s};double temp=2.0+rng()%9;
  for(int depth=start;!active.empty()&&depth<=need;depth++){
   int total=depth+1+b.mid.size();if(total>best){best=total;auto p=decode(b.mid,active[0]);if((int)p.size()!=best+1)abort();
    cout<<"BEST "<<best<<" round "<<r<<" vertices";for(int x:p)cout<<" "<<x;cout<<endl;}
   if(depth==need)return 0;
   vector<State>next;unordered_set<U>seen;for(auto&t:active){
    int l=targetL-t.len[0],right=need-targetL-t.len[1];int side=l==0?1:right==0?0:(l>right?0:1);
    for(int d=0;d<8;d++){int v=t.tip[side]^1<<d;State child=t;if(!step(child,side,v))continue;nodes++;
     if(!seen.insert(hashstate(child)).second)continue;int remain=need-depth-1;
     int capacity=evaluate(child,remain,0,targetL-child.len[0]);if(capacity<0){pruned++;continue;}
     int options=0;for(int a=0;a<2;a++)for(int j=0;j<4;j++)options+=std::popcount(child.avail.a[j]&nbr[child.tip[a]].a[j]&~nbr[child.tip[1-a]].a[j]);
     child.quality=capacity+0.55*options+temp*(rng()%1000000)/1000000.;next.push_back(child);
    }}
   if((int)next.size()>width){nth_element(next.begin(),next.begin()+width,next.end(),[](const State&a,const State&b){return a.quality>b.quality;});next.resize(width);}active.swap(next);
  }
  if((r+1)%100==0)cout<<"progress "<<r+1<<" best "<<best<<" nodes "<<nodes<<" pruned "<<pruned<<endl;
 }cout<<"DONE "<<rounds<<" best "<<best<<" nodes "<<nodes<<" pruned "<<pruned<<endl;
}
