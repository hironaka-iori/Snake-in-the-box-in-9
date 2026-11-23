#define PORTS_LIBRARY
#include "../search_q9_port_matching.cpp"
#include <bitset>
#include <unordered_map>
#include <map>
using Mask=bitset<512>;
constexpr int M=12;
array<Mask,512> halo;
int defects(const Path&p){
 array<int,512> when;when.fill(-1);int chords=0;
 for(int i=0;i<(int)p.size();i++){int v=p[i];assert(v>=0&&v<512&&when[v]<0);
  if(i)assert(distanceQ(v,p[i-1])==1);for(int k=0;k<9;k++)if(when[v^(1<<k)]>=0&&when[v^(1<<k)]+1<i)chords++;when[v]=i;}return chords;
}
struct Trace{Path p;string w;Trace(Path q):p(std::move(q)){for(int j=1;j<(int)p.size();j++)w+=char(countr_zero(unsigned(p[j]^p[j-1])));}};
uint64_t motif(const string&s,int i){array<int,9> labels{};int n=0;uint64_t out=0;for(int k=i;k<i+M;k++){int v=s[k];if(!labels[v])labels[v]=++n;out=16*out+labels[v];}return out;}
struct Arc{Path p;Mask used,boundary;int donor,j,first,last,side;bool changed;};
struct Run{
 mt19937 rng;vector<Trace> bank;unordered_map<uint64_t,vector<int>> buckets;int goal=192; bool wide=false;
 uint64_t jobs=0,aligns=0,validarcs=0,distinctarcs=0,setups=0,joins=0,unknown=0,nodes=0,inputrows=0,filled=0,multichange=0,attempts=0;
 set<int> sources,templates;
 Run(unsigned seed):rng(seed){for(int x=0;x<512;x++){halo[x].set(x);for(int k=0;k<9;k++)halo[x].set(x^(1<<k));}}
 void append(Path q){bank.emplace_back(q);reverse(q.begin(),q.end());bank.emplace_back(std::move(q));}
 void index(){for(int k=0;k<bank.size();k++){auto &w=bank[k].w;for(int i=0;i+M<=w.size();i++)buckets[motif(w,i)].push_back(k*256+i);}}
 bool make(const Trace& tmpl,int s,int t,int k,const Trace& don,int j,int a,int b,int donor,Arc&z){
  aligns++;if(a<0||b>=don.p.size()||a>j||b<j+M)return false;
  array<int,9> mp,back;mp.fill(-1);back.fill(-1);
  auto bind=[&](int x,int v){if(mp[x]<0&&back[v]<0){mp[x]=v;back[v]=x;}};
  for(int h=0;h<M;h++){bind(don.w[j+h],tmpl.w[k+h]);assert(mp[int(don.w[j+h])]==tmpl.w[k+h]);}
  array<array<int,9>,9> count{};for(int i=s;i<t;i++){int h=j+i-k;if(h>=0&&h<don.w.size())count[int(don.w[h])][int(tmpl.w[i])]++;}
  for(int rep=0;rep<9;rep++){
   int best=-1,x=-1,y=-1;for(int i=0;i<9;i++)if(mp[i]<0)for(int f=0;f<9;f++)if(back[f]<0&&count[i][f]>best){x=i;y=f;best=count[i][f];}if(x<0)break;bind(x,y);
  }
  z.donor=donor/2;z.side=donor%2;z.j=j;z.first=a;z.last=b;
  int v=tmpl.p[k];for(int h=j;h>a;h--)v^=1<<mp[int(don.w[h-1])];
  for(int h=a;h<=b;h++){
   if(h>a)v^=1<<mp[int(don.w[h-1])];
   // closed neighborhoods of all but the preceding vertex prohibit chords and duplicates.
   if(h>a&&z.used[v])return false;
   if(h>a&&((z.used&halo[v]).count()!=1))return false;
   z.p.push_back(v);z.used.set(v);z.boundary|=halo[v];
  }
  z.changed=z.p!=Path(tmpl.p.begin()+s,tmpl.p.begin()+t+1);validarcs++;return true;
 }
 bool solve(const array<Arc*,4>& combo,int templateId,int budget,int routes,bool control){
  int n=0,ch=0;Path raw;vector<pair<int,int>> pieces;
  for(auto*z:combo){int a=raw.size();raw.insert(raw.end(),z->p.begin(),z->p.end());pieces.emplace_back(a,raw.size()-1);n+=z->p.size();ch+=z->changed;}
  int need=goal+1-n;if(need<0||need>44)return false;
  // Try every order/orientation; an order needs at least sum(distance minus one) bridge vertices.
  array<int,4> ord{0,1,2,3};bool can=false;
  do{if(ord.front()>ord.back())continue;for(int f=0;f<16;f++){int low=0;for(int i=1;i<4;i++){
   auto &a=combo[ord[i-1]]->p,&b=combo[ord[i]]->p;int v=(f>>(i-1)&1)?a.front():a.back(),w=(f>>i&1)?b.back():b.front();low+=distanceQ(v,w)-1;}
   if(low<=need){can=true;break;}}if(can)break;}while(next_permutation(ord.begin(),ord.end()));
  if(!can)return false;
  setups++;
  if(wide&&ch==4&&setups%199==0){cout<<"FIELD "<<templateId;for(auto*z:combo)cout<<" "<<z->donor<<"/"<<z->side<<"/"<<z->first<<"-"<<z->last;cout<<" vertices";for(int v:raw)cout<<" "<<v;cout<<endl;}
  multichange+=(ch==4);Ports port;bool ok=port.run(raw,pieces,goal,need+1,need,budget,routes);nodes+=port.nodes;unknown+=port.incomplete||port.cutoff;
#ifdef REPLAY_PORT_CAPS
  if(!ok&&(port.incomplete||port.cutoff)){cout<<"REPLAY "<<templateId;for(auto*z:combo)cout<<" "<<z->donor<<"/"<<z->side<<"/"<<z->first<<"-"<<z->last;cout<<" vertices";for(int v:raw)cout<<" "<<v;cout<<endl;}
#endif
  if(!ok)return false;
  assert(valid(port.witness));cout<<(control?"CONTROL":"FOUND")<<" template "<<templateId<<" donors";for(auto*z:combo)cout<<" "<<z->donor<<"/"<<z->side<<"/"<<z->first<<"-"<<z->last;cout<<" changed "<<ch<<" vertices";for(int v:port.witness)cout<<" "<<v;cout<<endl;return true;
 }
 bool trial(int id,const Trace& tmpl,int picks,int cap,bool control){
  jobs++;templates.insert(id);int end=tmpl.p.size()-1;
  array<int,3> cut{int(end/4),int(end/2),int(3*end/4)};
  array<pair<int,int>,4> intervals;int start=0;for(int i=0;i<3;i++){int pos=cut[i]+(control?0:int(rng()%25)-12),g=control?3:1+rng()%(wide?12:6);intervals[i]={start,pos-1};start=pos+g;}intervals[3]={start,end};
  array<vector<Arc>,4> opts;
  for(int part=0;part<4;part++){
   auto [s,t]=intervals[part];if(t-s<M)return false;set<Path> seen;
   for(int i=0;i<(control?1:picks);i++){
    int k=control?(s+t-M)/2:s+rng()%(t-s-M+1);int donor,j;
    if(control){donor=2*part;j=k;}
    else{auto &b=buckets.at(motif(tmpl.w,k));int idx=b[rng()%b.size()];donor=idx/256;j=idx%256;if(donor/2==id)continue;}
    int a=j+s-k,b=j+t-k;if(!control&&rng()%8<3){if(part&&rng()%2)a+=int(rng()%5)-2;else if(part<3)b+=int(rng()%5)-2;}
    Arc z;if(!make(tmpl,s,t,k,bank[donor],j,a,b,donor,z))continue;
    if(seen.insert(z.p).second)opts[part].push_back(std::move(z));
   }
   distinctarcs+=opts[part].size();if(opts[part].empty())return false;shuffle(opts[part].begin(),opts[part].end(),rng);
  }
  filled++;int tries=0;
  for(auto &a:opts[0])for(auto &b:opts[1]){if(a.donor==b.donor||(a.boundary&b.used).any())continue;
   for(auto &c:opts[2]){if(c.donor==a.donor||c.donor==b.donor||((a.boundary|b.boundary)&c.used).any())continue;
    for(auto &d:opts[3]){if(d.donor==a.donor||d.donor==b.donor||d.donor==c.donor||((a.boundary|b.boundary|c.boundary)&d.used).any())continue;
     int n=a.changed+b.changed+c.changed+d.changed;if(!control&&n<2)continue;
     attempts++;for(auto*z:{&a,&b,&c,&d})sources.insert(z->donor);
     if(solve({&a,&b,&c,&d},id,18000,350,control))return true;
     if(++tries>=cap)return false;
   }}
  }return false;
 }
};
int main(int argc,char**argv){if(argc!=5&&argc!=6)return 2;int jobs=stoi(argv[1]),picks=stoi(argv[2]),cap=stoi(argv[3]);Run r(stoul(argv[4]));r.wide=argc==6;string w;Path clean;
 while(cin>>w){Path p{0};for(char c:w){assert(c>='0'&&c<='8');p.push_back(p.back()^(1<<(c-'0')));}int d=defects(p);if(!jobs&&clean.empty()){clean=p;continue;}if(d==1)r.append(p);}
 r.index();if(!jobs){assert(r.bank.size()==8&&clean.size()==192);r.goal=191;return r.trial(-1,Trace(clean),1,1,true)?0:4;}
 assert(r.bank.size()==4118);for(int i=0;i<jobs;i++){int id=i%2059;int k=2*id+(i/2059)%2;if(r.trial(id,r.bank[k],picks,cap,false))return 0;}
 cout<<"DONE template_draws "<<r.jobs<<" unique_templates "<<r.templates.size()<<" aligned_proposals "<<r.aligns<<" valid_arcs "<<r.validarcs<<" unique_arcs_per_domain "<<r.distinctarcs<<" four_nonempty_domains "<<r.filled<<" compatible_quadruples "<<r.attempts<<" port_systems "<<r.setups<<" all_four_changed_systems "<<r.multichange<<" incomplete "<<r.unknown<<" csp_nodes "<<r.nodes<<" source_rows_in_quadruples "<<r.sources.size()<<endl;
}
