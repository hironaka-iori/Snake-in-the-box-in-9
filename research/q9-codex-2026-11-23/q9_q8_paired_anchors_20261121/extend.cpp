#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Mask=bitset<512>;
array<Mask,512> nearv;
struct Seed{int donor,off,mother,shift,n;string pick;};
struct State{Mask blocked;array<char,192> steps{};int head,tail,lo,hi;};
struct Next{int rank,source,d1,d2;bool left;};
vector<string> bank,mother;mt19937 rnd;long long tried,legal;
bool clean(const State& s,int cur,int far,int d1,int d2){
 int a=cur^(1<<d1),b=a^(1<<d2);
 return !s.blocked[a]&&!s.blocked[b]&&!nearv[far][a]&&!nearv[far][b];
}
void append(State &s,bool left,int d1,int d2){
 int pos=left?s.head:s.tail,a=pos^(1<<d1),b=a^(1<<d2);s.blocked|=nearv[pos]|nearv[a];
 if(left){--s.lo;s.steps[2*s.lo]=char('0'+d2);s.steps[2*s.lo+1]=char('0'+d1);s.head=b;}
 else{s.steps[2*s.hi]=char('0'+d1);s.steps[2*s.hi+1]=char('0'+d2);++s.hi;s.tail=b;}
}
int main(int argc,char**argv){
 if(argc!=8)return 2;for(int v=0;v<512;v++){nearv[v].set(v);for(int i=0;i<9;i++)nearv[v].set(v^(1<<i));}
 ifstream ar("../q9_gap_generations/prior191.words"),ma("mothers.tsv"),se(argv[1]);ofstream out(argv[2]);string w;int id,r,z,t;
 while(ar>>w)bank.push_back(w);while(ma>>id>>r>>z>>t>>w)mother.push_back(w);
 vector<Seed> seeds;Seed e;while(se>>e.donor>>e.off>>e.mother>>e.shift>>e.n>>e.pick)seeds.push_back(e);
 int width=stoi(argv[3]),take=stoi(argv[4]),reps=stoi(argv[5]),control=stoi(argv[7]),record=0;rnd.seed(stoi(argv[6]));int jobs=0,found=0;
 for(int i=0;i<min(take,(int)seeds.size());i++)for(int rep=0;rep<reps;rep++){
  e=seeds[i];const auto& m=mother[e.mother];array<int,8> mp;mp.fill(-1);vector<int> free={0,1,2,3,4,5,6,7,8};
  for(int j=0;j<e.n;j++)mp[m[e.shift+j]-'0']=e.pick[j]-'0';
  erase_if(free,[&](int x){return find(mp.begin(),mp.end(),x)!=mp.end();});shuffle(free.begin(),free.end(),rnd);
  for(auto &q:mp)if(q<0){q=free.back();free.pop_back();}
  int L=(control==1||control==3)?e.shift:0,H=(control==1||control==2)?e.shift+e.n:96;
  int cutL=control==1?3+i%4:0,cutR=control==1?3+(i/4)%4:0;
  State a;a.lo=e.shift+cutL;a.hi=e.shift+e.n-cutR;a.head=a.tail=0;int v=0;
  for(int j=2*a.lo;j<2*a.hi;j++){char c=bank[e.donor][e.off+j-2*e.shift];a.steps[j]=c;v^=1<<(c-'0');if(j+1<2*a.hi)a.blocked|=nearv[v];}a.tail=v;
  vector<State> beam{a};State best=a;int choose=rep%4;int before=a.hi-a.lo;
  while(!beam.empty()){
   if(beam.front().hi-beam.front().lo>best.hi-best.lo)best=beam.front();
   if(best.lo==L&&best.hi==H)break;
   vector<Next> opts;opts.reserve(beam.size()*15);int pack=2+rep%6;
   for(int bi=0;bi<(int)beam.size();bi++){auto &q=beam[bi];bool left=choose==0?q.lo-L>H-q.hi:choose==1?q.lo>L:choose==2?q.hi>=H:((q.hi-q.lo-before+i)%2==0);
    if(q.lo==L)left=false;if(q.hi==H)left=true;
    int cur=left?q.head:q.tail,far=left?q.tail:q.head,pos=left?q.lo-1:q.hi,k=mp[m[pos]-'0'];
    for(int d=0;d<9;d++)if(d!=k)for(int order=0;order<2;order++){
     ++tried;int d1=order?d:k,d2=order?k:d;if(!clean(q,cur,far,d1,d2))continue;
     ++legal;int u=cur^(1<<d1),vv=u^(1<<d2);
     auto blocked=q.blocked|nearv[cur]|nearv[u];int degree=0;for(int x=0;x<9;x++)degree+=!blocked[vv^(1<<x)]&&!nearv[far][vv^(1<<x)];
     int score=-(int)blocked.count()*pack+degree*5+(int)(rnd()%27);
     int j=e.off+2*(pos-e.shift);
     if(rep%3==0&&j>=0&&j+1<191){
      int first=bank[e.donor][j+left]-'0',second=bank[e.donor][j+!left]-'0';score+=5*((d1==first)+(d2==second));}
     opts.push_back({score,bi,d1,d2,left});
    }
   }
   sort(opts.begin(),opts.end(),[](auto&a,auto&b){return a.rank>b.rank;});vector<State> next;next.reserve(width);unordered_set<size_t> visited;
   for(auto &p:opts){State q=beam[p.source];append(q,p.left,p.d1,p.d2);size_t h=hash<Mask>{}(q.blocked)^(q.head*521ull+q.tail)*0x9e3779b97f4a7c15ull;
    if(visited.insert(h).second)next.push_back(move(q));if((int)next.size()==width)break;}
   beam.swap(next);
  }
  ++jobs;int n=best.hi-best.lo;string word(best.steps.begin()+2*best.lo,best.steps.begin()+2*best.hi),mapping;for(int k:mp)mapping+=char('0'+k);
  out<<i<<' '<<rep<<' '<<L<<' '<<H<<' '<<a.lo<<' '<<a.hi<<' '<<best.lo<<' '<<best.hi<<' '<<mapping<<' '<<word<<'\n';
  found+=best.lo==L&&best.hi==H;
  if(n>record){record=n;cerr<<"best_pairs "<<n<<" seed "<<i<<" repeat "<<rep<<endl;}
  if((control==2||control==3)&&best.lo==L&&best.hi==H){int k=0;for(const auto& alt:beam){if(!k++){continue;}if(k>24)break;string v(alt.steps.begin()+2*alt.lo,alt.steps.begin()+2*alt.hi);out<<i<<' '<<rep<<' '<<L<<' '<<H<<' '<<a.lo<<' '<<a.hi<<' '<<alt.lo<<' '<<alt.hi<<' '<<mapping<<' '<<v<<'\n';}} 
  if(n==96)goto done;
 }
 done: cout<<"jobs "<<jobs<<" candidates "<<tried<<" legal "<<legal<<" max_pairs "<<record<<" target_reached "<<found<<endl;
}
