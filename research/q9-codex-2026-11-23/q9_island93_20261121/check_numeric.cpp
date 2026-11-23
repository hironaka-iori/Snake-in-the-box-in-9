#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
struct Face {int mask=0;array<int,8> exp{};array<int,256> cmp{};array<array<int,8>,256> price{};};
struct Pattern {int selected;array<int,8> incidence{};};
int main(){
 ios::sync_with_stdio(false);cin.tie(nullptr);
 vector<Pattern> forest;
 for(int m=0;m<256;m++){
    Pattern r{m};int pending=m;bool good=true;
    for(int v=0;v<8;v++)if(m>>v&1){for(int k=0;k<3;k++)if(m>>(v^(1<<k))&1)r.incidence[v]|=1<<k;if(popcount(unsigned(r.incidence[v]))>2)good=false;}
    while(good&&pending){int v=countr_zero(unsigned(pending)),todo=1<<v,points=0,degrees=0;
       while(todo){int u=countr_zero(unsigned(todo));todo&=todo-1;if(!(pending>>u&1))continue;pending^=1<<u;++points;
          int s=r.incidence[u];degrees+=popcount(unsigned(s));for(int k=0;k<3;k++)if(s>>k&1)todo|=(1<<(u^1<<k));}
       if(degrees!=2*(points-1))good=false;
    }
    if(good)forest.push_back(r);
 }
 int row,code,nlow,ports,eps,epc,delta,scale,bal,f0,f1,na,nw;long long reported;
 while(cin>>row>>code>>nlow>>ports>>eps>>epc>>delta>>scale>>bal>>f0>>f1>>na>>nw>>reported){
    array<bool,256> lower{},port{};for(int j=0,x;j<nlow;j++){cin>>x;assert(!lower[x]);lower[x]=true;}for(int j=0,x;j<ports;j++){cin>>x;assert(lower[x]&&!port[x]);port[x]=true;}
    vector<Face> axes(na);array<int,256> id;id.fill(-1);
    for(int k=0;k<na;k++){auto&a=axes[k];cin>>a.mask;assert(id[a.mask]<0&&popcount((unsigned)a.mask)==3);id[a.mask]=k;
       int j=0;for(int d=0;d<8;d++)if(a.mask>>d&1){for(int pat=0;pat<8;pat++)if(pat>>j&1)a.exp[pat]|=1<<d;for(int s=0;s<256;s++)if(s>>d&1)a.cmp[s]|=1<<j;++j;}}
    for(int j=0;j<nw;j++){int mask,v,s,p;cin>>mask>>v>>s>>p;assert(id[mask]>=0&&(s&~mask)==0&&v>=0&&v<256);auto&a=axes[id[mask]];assert(a.price[v][a.cmp[s]]==0&&p!=0);a.price[v][a.cmp[s]]=p;}
    const long long impossible=-(1LL<<50);long long bound=(long long)nlow*scale+(long long)delta*bal+eps*(epc?f1:f0);
    bool infeasible=false;vector<array<int,256>> valid(na);
    for(int v=0;v<256;v++){
      if(lower[v]&&!port[v])continue;int ns=0,parity=popcount(unsigned(v))%2;for(int d=0;d<8;d++){int x=v^1<<d;if(!lower[x]||port[x])ns|=1<<d;}
      long long maximum=port[v]?impossible:0;
      for(int size=0;size<=2;size++){int deg=size+port[v];if(deg!=2&&!(deg==1&&eps&&epc==1-parity))continue;
        auto eval=[&](int s){long long score=scale+(parity?bal:-bal)-(deg==1?(epc?f1:f0):0);
          for(int k=0;k<na;k++){auto&a=axes[k];int sg=a.cmp[s];score+=a.price[v][sg];valid[k][v]|=1<<sg;}maximum=max(maximum,score);};
        if(size==0)eval(0);else for(int d=0;d<8;d++)if(ns>>d&1){if(size==1)eval(1<<d);else for(int e=0;e<d;e++)if(ns>>e&1)eval(1<<d|1<<e);}
      }if(maximum==impossible)infeasible=true;bound+=maximum;
    }
    for(int k=0;k<na;k++){auto&a=axes[k];for(int base=0;base<256;base++)if(!(base&a.mask)){
       int must=0,forbid=0;for(int j=0;j<8;j++){int v=base+a.exp[j];must|=port[v]<<j;forbid|=(lower[v]&&!port[v])<<j;}
       long long maximum=impossible;for(auto& pat:forest){if((pat.selected&must)!=must||pat.selected&forbid)continue;bool ok=true;long long sc=0;int sel=pat.selected;
          while(sel){int j=countr_zero(unsigned(sel));sel&=sel-1;int v=base+a.exp[j],s=pat.incidence[j];if(!(valid[k][v]>>s&1)){ok=false;break;}sc-=a.price[v][s];}
          if(ok)maximum=max(maximum,sc);}
       if(maximum==impossible)infeasible=true;bound+=maximum;
    }}
    if(infeasible)bound=-1000000000000LL;assert(reported==bound);cout<<row<<' '<<code<<' '<<bound<<'\n';
 }
}
