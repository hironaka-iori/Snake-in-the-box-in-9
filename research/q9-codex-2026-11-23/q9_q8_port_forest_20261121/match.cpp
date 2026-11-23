#define main unused_extract_main
#include "extract.cpp"
#undef main
#include <fstream>
#include <unordered_map>
#include <numeric>
#include <sstream>
#include <set>
using U=unsigned long long;
const U W[9]={0,2744929691ull,901123807ull,112108396320897ull,3761697721691ull,4199243621ull,273421510010299ull,78231925153ull,76755179340009ull};
int hd(int a,int b){return popcount(unsigned(a^b));}
struct F{
 Bits b;vector<int> v,ports;int n,zeros;vector<U> loss;U base=0;
 F(Bits m):b(m){
  Forest f;if(!get(m,f))abort();v=f.vs;n=v.size();zeros=f.iso.size();ports=f.iso;ports.insert(ports.end(),f.ends.begin(),f.ends.end());loss.resize(ports.size());
  for(int i=0;i<ports.size();i++)for(int j=0;j<i;j++){U w=W[hd(ports[i],ports[j])];base+=w;loss[i]+=w;loss[j]+=w;}
 }
};
struct P{int f,i=-1,j=-1;};
vector<F> bank;
struct Ports{vector<int> v;Bits b{};};
Ports ports(P p){Ports r;auto& f=bank[p.f];for(int k=0;k<f.ports.size();k++)if(k!=p.i&&k!=p.j){r.v.push_back(f.ports[k]);put(r.b,f.ports[k]);}return r;}
struct Counters{U probes=0,hits=0,maps=0,portmaps=0,legalOverlap=0,cycles=0,found=0;};
struct Solver{
 Counters c;int minGoal;bool exact;
 bool place(const F&A,const F&B,const Ports&pa,const Ports&pb){
  // Choose port with rarest distance profile in the target.
  if(pa.v.empty()||pa.v.size()!=pb.v.size())return false;int na=pa.v.size();
  auto profiles=[](const auto& pts){vector<U> prof;for(int x:pts){U h=0;for(int y:pts)h+=W[hd(x,y)];prof.push_back(h);}return prof;};
  const auto ha=profiles(pa.v),hb=profiles(pb.v);
  int pos=0,rarity=300;
  for(int j=0;j<na;j++){int cnt=count(ha.begin(),ha.end(),hb[j]);if(!cnt)return false;if(cnt<rarity){rarity=cnt;pos=j;}}
  auto tensor=[](const auto& pts,int center,int freq[8][8]){for(int x:pts){int m=x^center;for(int a=0;a<8;a++)if((m>>a)&1)for(int b=0;b<=a;b++)if((m>>b)&1){freq[a][b]++;if(a!=b)freq[b][a]++;}}};
  int ob=pb.v[pos],cb[8][8]{};
  tensor(pb.v,ob,cb);
  for(int pivot=0;pivot<na;pivot++){
   if(ha[pivot]!=hb[pos])continue;
   int oa=pa.v[pivot],ca[8][8]{},cand[8]{},mapaxis[8]{},ord[8]{0,1,2,3,4,5,6,7};tensor(pa.v,oa,ca);
   for(int i=0;i<8;i++)for(int j=0;j<8;j++)if(cb[i][i]==ca[j][j])cand[i]|=1<<j;
   sort(ord,ord+8,[&](int i,int j){return popcount(unsigned(cand[i]))<popcount(unsigned(cand[j]));});
   auto rec=[&](auto&&self,int t,int used)->bool{
    if(t<8){int i=ord[t],opts=cand[i]&~used;while(opts){int j=countr_zero(unsigned(opts));opts&=opts-1;bool ok=true;
      for(int h=0;h<t;h++){int a=ord[h];if(cb[a][i]!=ca[mapaxis[a]][j]){ok=false;break;}}
      if(!ok)continue;mapaxis[i]=j;if(self(self,t+1,used|(1<<j)))return true;
    }return false;}
    c.maps++;
    int lo[16]{},hi[16]{};for(int m=1;m<16;m++){int j=countr_zero(unsigned(m));lo[m]=lo[m&(m-1)]^(1<<mapaxis[j]);hi[m]=hi[m&(m-1)]^(1<<mapaxis[4+j]);}
    auto tr=[&](int v){int m=ob^v;return oa^lo[m&15]^hi[m>>4];};
    for(int v:pb.v)if(!has(pa.b,tr(v)))return false;
    c.portmaps++;
    for(int v:B.v)if(!has(pb.b,v)&&has(A.b,tr(v)))return false;
    c.legalOverlap++;
    array<bool,512> present{};for(int v:A.v)present[v]=true;for(int v:B.v)present[256+tr(v)]=true;
    int tip=-1,ends=0;for(int v=0;v<512;v++)if(present[v]){
        int deg=0;for(int d=0;d<9;d++)deg+=present[v^(1<<d)];
        if(deg<1||deg>2)abort();if(deg==1){ends++;tip=v;}
    }
    if(ends!=2)abort();
    vector<int> q;int prev=-1;
    while(tip>=0){q.push_back(tip);int nxt=-1;for(int d=0;d<9;d++){int u=tip^(1<<d);if(present[u]&&u!=prev){nxt=u;break;}}prev=tip;tip=nxt;}
    if(q.size()!=A.n+B.n){c.cycles++;return false;}
    c.found++;cout<<"FOUND "<<q.size()-1;for(int v:q)cout<<" "<<v;cout<<endl;return true;
   };
   if(rec(rec,0,0))return true;
  }
  return false;
 }
 bool run(int split=-1){
  unordered_map<U,vector<P>>idx[2];
  auto variants=[](int id,int ends,auto call){
   auto&f=bank[id];int omit=ends-f.zeros;
   U h=f.base;int np=f.ports.size()-omit;
   if(np<1||omit<0||omit>2)return;
   U root=U(np)*159733467717121ull+h;
   if(!omit){call(root,P{id});return;}
   for(int i=f.zeros;i<f.ports.size();i++){
    if(omit==1)call(root-f.loss[i],P{id,i});
    else for(int j=f.zeros;j<i;j++)call(root-f.loss[i]-f.loss[j]+W[hd(f.ports[i],f.ports[j])],P{id,i,j});
   }
  };
  for(int e=0;e<=1;e++)for(int f=0;f<bank.size();f++)variants(f,e,[&](U h,P p){idx[e][h].push_back(p);});
  bool found=false;
  for(int f=0;f<bank.size();f++){
   for(int e=1;e<=2;e++)variants(f,e,[&](U h,P p){
    if(found)return;c.probes++;auto it=idx[2-e].find(h);if(it==idx[2-e].end())return;
    auto pa=ports(p);
    for(auto b:it->second){
     if(split>=0 && (p.f<split)==(b.f<split))continue;
     if(e==1&&tie(b.f,b.i,b.j)>tie(p.f,p.i,p.j))continue;
     int n=bank[p.f].n+bank[b.f].n;if(exact?n!=minGoal+1:n<minGoal+1)continue;
     c.hits++;if(place(bank[p.f],bank[b.f],pa,ports(b))){found=true;return;}
    }
   });
   if(found)return true;
   if(f%500==499)cout<<"AT "<<f+1<<" "<<c.hits<<" "<<c.maps<<" "<<c.portmaps<<" "<<c.legalOverlap<<endl;
  }
  return false;
 }
};
#ifndef Q8_CROSS_DRIVER
int main(int argc,char**argv){if(argc<4)return 2;set<Bits> all;
 for(int i=3;i<argc;i++){ifstream in(argv[i]);string l;while(getline(in,l)){istringstream ss(l);string t;ss>>t;if(t!="F")continue;int v;for(int j=0;j<4;j++)ss>>v;Bits b{};for(auto&x:b)ss>>x;all.insert(b);}}
 for(auto b:all)bank.emplace_back(b);
 Solver s{};s.minGoal=stoi(argv[1]);s.exact=stoi(argv[2]);bool found=s.run();auto c=s.c;
 cout<<"DONE "<<bank.size()<<" "<<found<<" "<<c.probes<<" "<<c.hits<<" "<<c.maps<<" "<<c.portmaps<<" "<<c.legalOverlap<<" "<<c.cycles<<endl;
}

#endif
