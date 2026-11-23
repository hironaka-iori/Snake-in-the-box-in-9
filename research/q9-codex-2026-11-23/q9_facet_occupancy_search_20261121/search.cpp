#define main earlier_occupancy_main
#include "../q9_occupancy_swaps_20261121/search.cpp"
#undef main
#include <limits>
const array<int,10> cost={7,0,0,9,18,27,36,45,54,63};
int side(int v){return popcount((unsigned)v)&1;}
struct Delta{int defect=0;array<int,2> tips{};};
struct Job{int id,goal,major;array<Mask,3> parts;array<int,512> lp;};
bool has(const Mask&m,int x){return m[x/64]>>(x%64)&1;}
vector<int> points(const Mask&m){vector<int> q;for(int i=0;i<512;++i)if(has(m,i))q.push_back(i);return q;}
struct Move{int x,y,local;double rank;};
struct Run{
 Job &job;State s,champ;vector<int> eligible;array<int,512> taboo{},prior;array<int,2> want{};int energy=0,best=999999,first=0;
 int attempts=0,applied=0,topocalls=0,shakes=0;long long pairs=0;
 Run(Job&j):job(j),s(points(j.parts[2])),champ(s),eligible(points(j.parts[1])),prior(j.lp){
  for(int i=0;i<512;++i)if(has(j.parts[0],i)&&!s.on[i])abort();
  want=j.goal%2?array<int,2>{1,1}:array<int,2>{0,0};if(!(j.goal%2))want[j.major]=2;
 }
 int ends(int e,int o){return 3*(abs(e-want[0])+abs(o-want[1]));}
 int local(const State&a){
  int l=0;array<int,2> t{};for(int x=0;x<512;++x)if(a.on[x]){l+=cost[a.load[x]];t[side(x)]+=a.load[x]==1;}
  return l+ends(t[0],t[1]);
 }
 int full(const State&a){auto top=a.inspect();++topocalls;return local(a)+5*(top.groups-1)+6*top.cycles;}
 void report(int run,int iter,bool hit){
  auto t=champ.inspect(true);cout<<(hit?"FOUND":"BEST")<<" "<<job.id<<" "<<run<<" "<<iter<<" "<<first<<" "<<best<<" "<<applied<<" "<<pairs<<" "<<topocalls<<" "<<shakes<<" "<<t.groups<<" "<<t.cycles;
  for(auto m:champ.mask)cout<<" "<<m;
  if(hit){
   auto p=t.longest;if(p.size()!=job.goal+1)abort();
   for(int i=0;i<p.size();++i)for(int j=0;j<i;++j)if(!((i==j+1)==has_single_bit(unsigned(p[i]^p[j])))||p[i]==p[j])abort();
   for(int x:p)cout<<" "<<x;
  }cout<<endl;
 }
 void diversify(int it){
  s=champ;taboo.fill(0);int count=1+pick(4);
  for(int h=0;h<count;++h){
   int x,y;do{x=eligible[pick(eligible.size())];}while(!s.on[x]||has(job.parts[0],x));
   do{y=eligible[pick(eligible.size())];}while(s.on[y]||side(x)!=side(y));
   s.edit(x,-1);s.edit(y,1);taboo[x]=it+5;taboo[y]=it+5;
  }++shakes;energy=full(s);
 }
 bool solve(int run,int steps){
  best=energy=first=full(s);if(!best){champ=s;report(run,0,true);return true;}
  for(int it=1;it<=steps;++it){
   if(it!=1&&it%83==0)diversify(it);
   int f=0;array<int,2> ts{};array<Delta,512> change;array<vector<int>,2> add,del;
   for(int x:eligible){
    int d=s.load[x],b=side(x);if(s.on[x]){f+=cost[d];ts[b]+=d==1;}
    if(has(job.parts[0],x))continue;
    int sg=s.on[x]?-1:1;
    (sg>0?add[b]:del[b]).push_back(x);
    Delta &z=change[x];z.defect=sg*cost[d];z.tips[b]=sg*(d==1);
    for(int k=0;k<9;++k){int y=x^(1<<k);if(!s.on[y])continue;int n=s.load[y];
     z.defect+=cost[n+sg]-cost[n];z.tips[b^1]+=(n+sg==1)-(n==1);
    }
   }
   vector<Move> opts;constexpr int keep=8;int worst=0;double gate=1e10;
   for(int b=0;b<2;++b)for(int x:del[b])for(int y:add[b]){
    ++pairs;auto&a=change[x];auto&c=change[y];int localf=f+a.defect+c.defect;
    int e=ts[0]+a.tips[0]+c.tips[0],o=ts[1]+a.tips[1]+c.tips[1];
    int d=x^y;if(has_single_bit(unsigned(d&(d-1)))){
     int corr=0;for(int mm=d;mm;mm&=mm-1){int u=x^(mm&-mm);if(s.on[u]){
       int k=s.load[u];localf+=2*cost[k]-cost[k-1]-cost[k+1];corr+=2*(k==1)-(k-1==1)-(k+1==1);}}
     (b?e:o)+=corr;
    }
    int loc=localf+ends(e,o);
    int tabu=max(taboo[x],taboo[y])>it;
    double rank=loc+((tabu&&loc>=best)?18.:0.)+((prior[x]-prior[y])/1000.)*.25;
    if(rank>gate)continue;
    rank+=double(rng()&65535)/65536.*3.0;if(rank>gate)continue;
    Move m{x,y,loc,rank};if(opts.size()<keep)opts.push_back(m);else opts[worst]=m;
    if(opts.size()==keep){worst=0;for(int j=1;j<keep;++j)if(opts[j].rank>opts[worst].rank)worst=j;gate=opts[worst].rank;}
   }
   if(opts.empty())abort();
   Move choice=opts.front();double minval=1e20;int newenergy=0;
   for(auto m:opts){
    s.edit(m.x,-1);s.edit(m.y,1);auto t=s.inspect();++topocalls;int exact=m.local+5*(t.groups-1)+6*t.cycles;
    if(it==1&&local(s)!=m.local)abort();
    double val=exact+m.rank-m.local+double(rng()&255)/1024;
    if(val<minval){minval=val;newenergy=exact;choice=m;}
    if(exact<best){champ=s;best=exact;if(best==0){report(run,it,true);return true;}}
    s.edit(m.y,-1);s.edit(m.x,1);
   }
   s.edit(choice.x,-1);s.edit(choice.y,1);energy=newenergy;++applied;
   int tenure=3+pick(9);taboo[choice.x]=it+tenure;taboo[choice.y]=it+tenure;
  }
  if(full(champ)!=best)abort();report(run,steps,false);return false;
 }
};
#ifndef Q9_OCCUPANCY_LIBRARY
int main(int argc,char**argv){
 if(argc!=4)return 2;int rounds=stoi(argv[1]),steps=stoi(argv[2]);rng.seed(stoul(argv[3]));Job j;
 while(cin>>j.id>>j.goal>>j.major){for(auto &m:j.parts)for(auto &x:m)cin>>x;for(int &v:j.lp)cin>>v;
  for(int k=0;k<rounds;++k){Run a(j);if(a.solve(k,steps)){if(j.goal==192)return 0;break;}}
 }
}

#endif
