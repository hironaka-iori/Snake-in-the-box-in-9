// Reassemble independently chosen database segments at both ends of a middle segment.
#define Q9_FREE_BRIDGE_JOIN_NO_MAIN
#include "search_q9_free_bridge_join.cpp"
#include <bit>
#include <fstream>
#include <numeric>
#include <random>
#include <set>
using Mask=array<uint64_t,8>;
struct Option{Mask selected{},forbidden{};Path seq;};
mt19937 rng;
void addbit(Mask&m,int x){m[x>>6]|=1ULL<<(x%64);}
bool disjoint(const Mask&a,const Mask&b){for(int j=0;j<8;j++)if(a[j]&b[j])return false;return true;}
vector<Path> load(const string&name){ifstream in(name);vector<Path>out;string line;while(getline(in,line)){istringstream s(line);Path p;int x;while(s>>x){if(x<0||x>=512)abort();p.push_back(x);}if(!p.empty()){if(!valid(p))abort();out.push_back(p);}}if(out.empty())abort();return out;}
Path key(const Path& w){int n=w.size()-1;return min(word(w,0,1,n),word(w,n,-1,n));}
bool try_extend(Path w){for(int pass=0;pass<2;pass++,reverse(w.begin(),w.end()))for(int d=0;d<9;d++){
 int z=w.back()^1<<d;bool ok=true;for(size_t j=0;j+1<w.size();j++)if(std::popcount((unsigned)(z^w[j]))<2){ok=false;break;}
 if(ok){w.push_back(z);if(!valid(w))abort();cout<<"FOUND "<<w.size()-1<<" vertices";for(int v:w)cout<<" "<<v;cout<<endl;return true;}
 }return false;}
void addSource(const Path&p,int bound){for(int i=0;i+1<(int)p.size();i++){int last=min(bound,(int)p.size()-i-1);auto w=word(p,i,1,last);int n=0;
 for(int b:w){if(!trie[n].child[b]){trie[n].active|=1<<b;trie[n].child[b]=trie.size();trie.emplace_back();}n=trie[n].child[b];}}}
struct Grow{
 int lo,hi,limit;long long cap,nodes=0;bool stopped=false;array<bool,512>ban{};array<int,9>mapping{},rank;vector<vector<Option>> options;Path tail;
 Grow(const Path&center,bool left,int lower,int upper,int lim,int budget):lo(lower),hi(upper),limit(lim),cap(budget),options(upper+1){
  int root=left?center.front():center.back();for(int x:center){ban[x]=true;if(x!=root)for(int b=0;b<9;b++)ban[x^1<<b]=true;}
  iota(rank.begin(),rank.end(),0);shuffle(rank.begin(),rank.end(),rng);visit(0,root,511);
 }
 void visit(int node,int x,int unused){
  if(++nodes>cap){stopped=true;return;}int len=tail.size();
  if(len>=lo&&(int)options[len].size()<limit){Option o;o.seq=tail;for(int v:tail){addbit(o.selected,v);addbit(o.forbidden,v);for(int d=0;d<9;d++)addbit(o.forbidden,v^1<<d);}options[len].push_back(move(o));}
  if(len>=hi)return;
  for(int b:rank){int k=trie[node].child[b];if(!k)continue;int old=mapping[b];
   int dirs=old?old:unused;for(int d:rank)if((dirs>>d)&1){int bit=1<<d,v=x^bit;if(ban[v])continue;
    mapping[b]=bit;tail.push_back(v);visit(k,v,unused&~bit);tail.pop_back();if(stopped)return;}
   mapping[b]=old;
  }
 }
};
int main(int argc,char**argv){
 if(argc!=10)return 2;auto donors=load(argv[1]),seeds=load(argv[2]);int goal=stoi(argv[3]),maxTail=stoi(argv[4]),cap=stoi(argv[5]),limit=stoi(argv[6]),runs=stoi(argv[7]);rng.seed(stoul(argv[8]));int banklimit=stoi(argv[9]);shuffle(donors.begin(),donors.end(),rng);if(banklimit>0&&(int)donors.size()>banklimit)donors.resize(banklimit);
 for(auto s:donors){addSource(s,maxTail);reverse(s.begin(),s.end());addSource(s,maxTail);}
 cout<<"INIT sources "<<donors.size()<<" prefix_nodes "<<trie.size()<<" seeds "<<seeds.size()<<endl;
 set<Path> known;bool novelty=getenv("Q9_SEEN_191")!=nullptr;
 if(novelty){if(goal!=191)abort();for(auto&w:load(getenv("Q9_SEEN_191")))known.insert(key(w));if(known.size()!=131)abort();}
 long long nodes=0,capped=0,joins=0,both=0,num=0;
 for(int trial=0;trial<runs;trial++){int id=rng()%seeds.size();auto &s=seeds[id];int n=s.size()-1;
  int minmiddle=max(goal-2*maxTail,64),maxmiddle=min(n,goal-30);if(minmiddle>maxmiddle)continue;
  int m=minmiddle+rng()%(maxmiddle-minmiddle+1),i=rng()%(n-m+1);Path mid(s.begin()+i,s.begin()+i+m+1);
  int rem=goal-m,minL=max(8,rem-maxTail),maxL=min(maxTail,rem-8);if(maxL<minL)continue;
  int t=minL+rng()%(maxL-minL+1);if(trial%3==0)t=clamp(i,minL,maxL);int lo=max(minL,t-2),hi=min(maxL,t+2);
  Grow left(mid,true,lo,hi,limit,cap);nodes+=left.nodes;capped+=left.stopped;bool any=false;for(auto &r:left.options)any|=!r.empty();
  if(any){Grow right(mid,false,rem-hi,rem-lo,limit,cap);nodes+=right.nodes;capped+=right.stopped;
   for(int a=lo;a<=hi;a++){auto &A=left.options[a],&B=right.options[rem-a];both+=!A.empty()&&!B.empty();num+=A.size()+B.size();
    for(auto &x:A)for(auto &y:B){joins++;if(!disjoint(x.forbidden,y.selected))continue;
     Path w(x.seq.rbegin(),x.seq.rend());w.insert(w.end(),mid.begin(),mid.end());w.insert(w.end(),y.seq.begin(),y.seq.end());
     if(!valid(w)||(int)w.size()!=goal+1)abort();if(novelty){if(!known.insert(key(w)).second)continue;
       cout<<"NEW191 vertices";for(int z:w)cout<<" "<<z;cout<<endl;if(try_extend(w))return 0;continue;}
     cout<<"FOUND "<<goal<<" mid "<<m<<" tails "<<a<<" "<<rem-a<<" vertices";for(int v:w)cout<<" "<<v;cout<<endl;return 0;}
   }}
  if((trial+1)%50==0)cout<<"progress "<<trial+1<<" nodes "<<nodes<<" capped "<<capped<<" both "<<both<<" embeddings "<<num<<" joins "<<joins<<endl;
 }cout<<"DONE "<<runs<<" nodes "<<nodes<<" capped "<<capped<<" both "<<both<<" embeddings "<<num<<" joins "<<joins<<endl;
}
