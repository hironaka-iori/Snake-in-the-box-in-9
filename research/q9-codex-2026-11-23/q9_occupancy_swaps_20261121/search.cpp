// Fixed-cardinality site swaps; moves and scores use occupation and adjacency only.
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
using Mask=array<unsigned long long,8>;
mt19937 rng;int pick(int n){return rng()%n;}
const int dim=9;
struct State{
 array<int,512> on{},load{};
 array<int,10> hist{};
 Mask mask{};
 State(const vector<int>& seed){for(int v:seed)edit(v,1);}
 void edit(int v,int sign){
  if(on[v]!=(sign<0))abort();
  if(sign<0)--hist[load[v]];
  on[v]=sign>0;mask[v/64]^=1ull<<(v%64);
  for(int d=0;d<dim;d++){int u=v^(1<<d);
   if(on[u])--hist[load[u]];
   load[u]+=sign;
   if(on[u])++hist[load[u]];
  }
  if(sign>0)++hist[load[v]];
 }
 int over()const{int s=0;for(int d=3;d<=9;d++)s+=(d-2)*hist[d];return s;}
 int local()const{return 7*over()+5*hist[0]+abs(hist[1]-2);}
 struct Topology{int groups=0,cycles=0;vector<int> longest;};
 Topology inspect(bool save=false)const{
  Topology t;Mask remaining=mask;int q[512];
  for(int block=0;block<8;block++)while(remaining[block]){
   int x=block*64+countr_zero(remaining[block]),head=0,tail=0,sum=0,tip=-1;bool linear=true;
   auto visit=[&](int v){remaining[v/64]&=~(1ull<<(v%64));q[tail++]=v;};visit(x);
   while(head<tail){
    int v=q[head++];sum+=load[v];linear&=load[v]<=2;if(load[v]<2)tip=v;
    for(int d=0;d<9;d++){int u=v^(1<<d);if((remaining[u/64]>>(u%64))&1)visit(u);}
   }
   ++t.groups;t.cycles+=sum/2-tail+1;
   if(save&&linear&&tip>=0&&tail>int(t.longest.size())){
    t.longest.clear();int last=-1;
    while(tip>=0){t.longest.push_back(tip);int nx=-1;
     for(int d=0;d<9;d++){int u=tip^(1<<d);if(u!=last&&on[u]){nx=u;break;}}
     last=tip;tip=nx;
    }
    if(t.longest.size()!=tail)abort();
   }
  }
  return t;
 }
 int choose_remove(int recent){
   int best=-9999,w=-1;
   for(int t=0;t<12;t++){
    int v;
    if(recent>=0&&t<5){v=recent^(1<<pick(9));if(pick(2))v^=1<<pick(9);if(!on[v])continue;}
    else{do v=pick(512);while(!on[v]);}
    int merit=load[v]>2?28:load[v]==0?18:load[v]==1?9:0;
    for(int d=0;d<9;d++){int u=v^(1<<d);merit+=on[u]&&load[u]>2?8:0;}
    merit+=pick(36);if(merit>best){best=merit;w=v;}
   }
   return w;
 }
 int choose_add(int removed,const vector<int>& forbid){
   int best=-99999,w=-1;
   for(int t=0;t<30;t++){
    int v;
    if(t<13){v=removed^(1<<pick(9))^(1<<pick(9));}
    else if(t<22){int tip;do tip=pick(512);while(!on[tip]);v=tip^(1<<pick(9));}
    else v=pick(512);
    if(on[v]||find(forbid.begin(),forbid.end(),v)!=forbid.end()||(__builtin_parity(unsigned(v^removed))))continue;
    int penalty=4*abs(load[v]-2)+3*max(0,load[v]-2);
    for(int d=0;d<9;d++){int u=v^(1<<d);if(on[u])penalty+=(load[u]>=2?5:-3);}
    int merit=pick(23)-penalty;if(merit>best){best=merit;w=v;}
   }
   if(w<0){do w=pick(512);while(on[w]||__builtin_parity(unsigned(w^removed))||find(forbid.begin(),forbid.end(),w)!=forbid.end());}
   return w;
 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;int N=stoi(argv[1]),epochs=stoi(argv[2]),steps=stoi(argv[3]);rng.seed(stoul(argv[4]));
 vector<vector<int>> seeds;string line;
 while(getline(cin,line)){istringstream ss(line);int x;vector<int>v;while(ss>>x)v.push_back(x);if(v.size()!=N||set<int>(v.begin(),v.end()).size()!=N)return 3;seeds.push_back(v);}
 if(seeds.empty())return 4;long long accepted[5]{},proposed[5]{},full=0,forest=0,disconnected=0;int best=999,bestcomponent=0;
 map<int,long long> forestgroups;set<Mask> archived;long long distinct_forest=0;
 for(int ep=0;ep<epochs;ep++){
  State start(seeds[ep%seeds.size()]),s=start,champ=s;
  auto z=s.inspect();int score=s.local()+3*(z.groups-1)+4*z.cycles,bestep=score;
  for(int it=0;it<steps;it++){
   if(it&&it%900==0&&pick(3)!=0){s=champ;score=bestep;}
   int kind=pick(100),n=kind<63?1:kind<88?2:kind<97?3:4;proposed[n]++;
   vector<int> rem,added;int recent=-1;
   for(int j=0;j<n;j++){int v=s.choose_remove(recent);s.edit(v,-1);rem.push_back(v);recent=v;}
   for(int v:rem){int w=s.choose_add(v,rem);s.edit(w,1);added.push_back(w);}
   int local=s.local();double temp=.40+2.15*(1.-(it%300)/300.);
   double gate=score-temp*log(max(1e-10,generate_canonical<double,32>(rng)));
   if(local<=gate){
    auto topo=s.inspect();full++;
    int candidate=local+3*(topo.groups-1)+4*topo.cycles;
    if(candidate<=gate){
     score=candidate;accepted[n]++;
     if(score<bestep||(score==bestep&&pick(5)==0)){champ=s;bestep=score;}
     if(score<best){best=score;cout<<"BEST "<<ep<<" "<<it<<" "<<score<<" "<<s.over()<<" "<<topo.groups<<" "<<topo.cycles<<endl;}
     if(topo.groups>1)disconnected++;
     if(!s.over()&&topo.cycles==0){
      forest++;forestgroups[topo.groups]++;
      if(archived.size()<200000&&archived.insert(s.mask).second){
       distinct_forest++;
       if(getenv("Q9_SAVE_TWO_FORESTS") && topo.groups==2){cout<<"SET";for(unsigned long long m:s.mask)cout<<" "<<m;cout<<char(10);}
       auto a=s.inspect(true);int length=a.longest.size()-1;
       bestcomponent=max(bestcomponent,length);
       if(length>=N-4){cout<<"PATH "<<length;for(int v:a.longest)cout<<" "<<v;cout<<'\n';}
       if(topo.groups==1){cout<<"FOUND "<<length<<endl;return 0;}
      }else if(topo.groups==1){auto a=s.inspect(true);cout<<"PATH "<<a.longest.size()-1;for(int v:a.longest)cout<<" "<<v;cout<<"\nFOUND "<<a.longest.size()-1<<endl;return 0;}
     }
     continue;
    }
   }
   for(int v:added)s.edit(v,-1);for(int v:rem)s.edit(v,1);
  }
  if(ep%30==29)cout<<"AT "<<ep+1<<" "<<best<<" "<<distinct_forest<<" "<<bestcomponent<<endl;
 }
 cout<<"DONE "<<epochs<<" "<<steps<<" "<<full<<" "<<forest<<" "<<distinct_forest<<" "<<disconnected<<" "<<bestcomponent<<" "<<best<<endl;
 for(int k=1;k<=4;k++)cout<<"MOVE "<<k<<" "<<proposed[k]<<" "<<accepted[k]<<endl;
 for(auto [k,v]:forestgroups)cout<<"FOREST "<<k<<" "<<v<<endl;
}
