#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
bool valid(const Path &p){
 for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){int x=p[i]^p[j];if(!x||((popcount(unsigned(x))==1)!=(j+1==i)))return false;}return true;
}
struct Host{
 const Path &p;int a,b;array<bool,512> before{},after{};
 Host(const Path &q,int left,int right):p(q),a(left),b(right){
  for(int j=0;j<=a;j++){int v=p[j];before[v]=true;for(int k=0;k<9;k++)before[v^(1<<k)]=true;}
  for(int j=0;j<a;j++){int v=p[j];after[v]=true;for(int k=0;k<9;k++)after[v^(1<<k)]=true;}
 }
 bool feasible(int sh)const{for(int j=b;j<(int)p.size();j++)if(before[p[j]^sh])return false;return true;}
 array<bool,512> blocked(int sh)const{auto bad=after;for(int j=b+1;j<(int)p.size();j++){int v=p[j]^sh;bad[v]=true;for(int k=0;k<9;k++)bad[v^(1<<k)]=true;}return bad;}
};
struct Test{
 const Path &p,&q;int a,b,j,l,shift,u,v,dis,goal;const array<bool,512>& bad;
 array<int,9> axis{},mp{};array<vector<pair<int,int>>,9> ready;int n=0;uint64_t &nodes;
 Test(const Host &h,const Path &don,int start,int len,int sh,const array<bool,512>&ban,uint64_t &count):
  p(h.p),q(don),a(h.a),b(h.b),j(start),l(len),shift(sh),u(p[a]),v(p[b]^sh),
  dis(q[j]^q[j+l]),goal(u^v),bad(ban),nodes(count){
  int done=0,all=0;for(int i=0;i<=l;i++)all|=q[j+i]^q[j];
  vector<bool> checked(l+1);checked[0]=checked[l]=true;
  while(done!=all){
   int best=-1,score=-1;
   for(int bits=all&~done;bits;bits&=bits-1){int bit=bits&-bits,z=done|bit,r=0;
    for(int t=1;t<l;t++)if(!checked[t]){int rel=q[j+t]^q[j];r+=((rel&~z)==0||((rel^dis)&~z)==0);}
    if(r>score){score=r;best=bit;}}
   axis[n]=countr_zero(unsigned(best));done|=best;
   for(int t=1;t<l;t++)if(!checked[t]){int rel=q[j+t]^q[j];if(!(rel&~done)){ready[n].push_back({rel,u});checked[t]=true;}
    else if(!((rel^dis)&~done)){ready[n].push_back({rel^dis,v});checked[t]=true;}}
   n++;
  }
 }
 int image(int mask)const{int out=0;while(mask){unsigned bit=countr_zero(unsigned(mask));out|=mp[bit];mask&=mask-1;}return out;}
 bool search(int depth,int free){
  if(depth==n)return true;
  int bit=axis[depth],allowed=free&((dis>>bit&1)?goal:511^goal);
  for(;allowed;allowed&=allowed-1){int f=allowed&-allowed;mp[bit]=f;nodes++;
   bool ok=true;for(auto [rel,anchor]:ready[depth])if(bad[anchor^image(rel)]){ok=false;break;}
   if(ok&&search(depth+1,free^f))return true;
  }return false;
 }
 Path recover(){Path out(p.begin(),p.begin()+a);for(int k=0;k<=l;k++)out.push_back(u^image(q[j]^q[j+k]));for(int k=b+1;k<(int)p.size();k++)out.push_back(p[k]^shift);assert(out[a]==p[a]&&out[a+l]==(p[b]^shift)&&valid(out));return out;}
};
int main(int argc,char**argv){
 if(argc<4||argc>5)return 2;bool reverse_donors=argc==5;int groups=stoi(argv[1]),per=stoi(argv[2]);mt19937 rng(stoul(argv[3]));vector<Path> bank;
 string line;while(cin>>line){Path p{0};for(char c:line){assert(c>='0'&&c<='8');p.push_back(p.back()^(1<<(c-'0')));}assert(p.size()==192&&valid(p));bank.push_back(p);}
 if(!groups){
  auto &p=bank[0];int sh=p[1]^p[5]^8;Path shortp(p.begin(),p.begin()+2);for(int k=5;k<(int)p.size();k++)shortp.push_back(p[k]^sh);assert(valid(shortp));
  Host h(shortp,1,2);assert(h.feasible(sh));auto bad=h.blocked(sh);uint64_t nodes=0;Test t(h,p,1,4,sh,bad,nodes);assert(t.search(0,511));auto out=t.recover();cout<<"CONTROL source "<<shortp.size()-1<<" result "<<out.size()-1<<" shift "<<sh<<" vertices";for(int v:out)cout<<" "<<v;cout<<endl;return 0;
 }
 auto rev=bank;for(auto &r:rev)reverse(r.begin(),r.end());
 uint64_t drawn=0,eligible=0,nodes=0,tested=0,zero=0,nonzero=0;int hosts=0,nonempty=0;
 for(int z=0;z<groups;z++){
  int host=rng()%bank.size();const auto &p=bank[host];int gain=reverse_donors?1:1+rng()%4;
  int span=4+rng()%133;int a=1+rng()%(190-span),b=a+span,l=span+gain;
  Host h(p,a,b);array<vector<int>,10> bydist;int viable=0;
  for(int sh=0;sh<512;sh++){int d=popcount(unsigned(p[a]^p[b]^sh));if((d^l)&1||d<2||!h.feasible(sh))continue;bydist[d].push_back(sh);viable++;}
  if(!viable)continue;nonempty++;hosts+=viable;
  for(int itr=0;itr<per;itr++){
   int donor=rng()%(bank.size()-1);if(donor>=host)donor++;const Path &don=(reverse_donors?rev:bank)[donor];
   int j=rng()%(don.size()-l);int d=popcount(unsigned(don[j]^don[j+l]));drawn++;
   if(bydist[d].empty())continue;eligible++;
   auto&shifts=bydist[d];int sh=shifts[rng()%shifts.size()];
   if(shifts[0]==0&&rng()%2==0)sh=0;
   auto bad=h.blocked(sh);Test t(h,don,j,l,sh,bad,nodes);tested++;if(sh)nonzero++;else zero++;
   if(!t.search(0,511))continue;auto out=t.recover();cout<<"FOUND host "<<host<<" interval "<<a<<" "<<b<<" donor "<<donor<<" start "<<j<<" len "<<l<<" shift "<<sh<<" vertices";
   for(int x:out)cout<<" "<<x;cout<<endl;return 0;
  }
 }
 cout<<"DONE recipient_intervals "<<groups<<" viable "<<nonempty<<" viable_shifts "<<hosts<<" donor_draws "<<drawn<<" compatible_displacements "<<eligible<<" tested "<<tested<<" zero_shift "<<zero<<" nonzero_shift "<<nonzero<<" assignment_nodes "<<nodes<<endl;
 return 0;
}
