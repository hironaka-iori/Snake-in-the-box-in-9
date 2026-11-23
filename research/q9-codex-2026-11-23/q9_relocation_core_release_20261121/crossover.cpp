#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <set>
#include <string>
#include <vector>
using namespace std;
using Mask=array<uint64_t,8>;using P=vector<int>;
inline void put(Mask&b,int v){b[v/64]|=uint64_t(1)<<(v%64);}
inline bool intersects(const Mask&a,const Mask&b){for(int i=0;i<8;i++)if(a[i]&b[i])return true;return false;}
inline bool covers(const Mask&a,const Mask&b,const Mask&c){for(int i=0;i<8;i++)if(c[i]&~(a[i]|b[i]))return false;return true;}
struct Slice{P p;vector<Mask>s,n;Slice(P path):p(path),s(193),n(193){for(int i=1;i<=192;i++){s[i]=s[i-1];put(s[i],p[i-1]);n[i]=n[i-1];if(i>=2)for(int d=0;d<9;d++)put(n[i],p[i-2]^(1<<d));}}};
struct Search{
 array<bool,512>ban{},taken{};array<int,512>adj{};P a,b,mid,l,r;int maxlen=0,id=0,sa,sb,orient1,orient2,outbest=-1;Mask host1{},host2{};set<string> seen;
 uint64_t tried=0,valid=0,bridges=0,calls=0,tips=0;bool found=false;
 void setv(int v,int x){taken[v]=x>0;for(int i=0;i<9;i++)adj[v^1<<i]+=x;}
 void extend(int x,int y,int length,bool left){
  if(found)return;tips++;if(length>maxlen||length>=191){P u(l.rbegin(),l.rend());u.insert(u.end(),a.begin(),a.end());u.insert(u.end(),mid.begin(),mid.end());u.insert(u.end(),b.rbegin(),b.rend());u.insert(u.end(),r.begin(),r.end());
   if((int)u.size()!=length+1)abort();
   bool emit=length>maxlen; const char* kind=emit?"BEST":"LONG";
   if(length>=191){string w;int n1=0,n2=0;for(int v:u){n1+=!(host1[v/64]>>(v%64)&1);n2+=!(host2[v/64]>>(v%64)&1);}for(int i=1;i<(int)u.size();i++)w+=char(48+countr_zero(unsigned(u[i]^u[i-1])));auto norm=[](string t){array<char,9> a{};char c=48;for(char&v:t){int d=v-48;if(!a[d])a[d]=c++;v=a[d];}return t;};string f=norm(w);reverse(w.begin(),w.end());emit|=seen.insert(min(f,norm(w))).second||min(n1,n2)>outbest;outbest=max(outbest,min(n1,n2));}
   if(emit){for(int i=0;i<(int)u.size();i++)for(int j=0;j<i;j++)if(u[i]==u[j]||(popcount(unsigned(u[i]^u[j]))==1)!=(j+1==i))abort();
   maxlen=max(maxlen,length);cout<<kind<<" "<<id<<" "<<length<<" "<<sa<<" "<<sb<<" "<<orient1<<" "<<orient2<<" "<<a.size()<<" "<<b.size()<<" "<<mid.size();for(int v:u)cout<<" "<<v;cout<<endl;}
  }if(length>=192){found=true;return;}
  if(left)extend(x,y,length,false);auto &arm=left?l:r;int z=left?x:y;
  for(int i=0;i<9&&!found;i++){int v=z^1<<i;if(taken[v]||ban[v]||adj[v]!=1)continue;setv(v,1);arm.push_back(v);extend(left?v:x,left?y:v,length+1,left);arm.pop_back();setv(v,-1);}
 }
 void bridge(int z,int budget){
  if(found)return;calls++;int goal=b.back(),d=popcount(unsigned(z^goal));
  if(d==1){bridges++;extend(a.front(),b.front(),a.size()+b.size()+mid.size()-1,true);return;}
  if((int)mid.size()+d-1>budget)return;
  for(int i=0;i<9&&!found;i++){int v=z^1<<i;if(ban[v]||taken[v])continue;bool closing=popcount(unsigned(v^goal))==1;if(adj[v]!=1+int(closing))continue;setv(v,1);mid.push_back(v);bridge(v,budget);mid.pop_back();setv(v,-1);}
 }
};
int main(){ifstream f("placements.txt");string line;array<vector<P>,120>paths;while(getline(f,line)){istringstream in(line);int rank,t,score,src,j,di,v;in>>rank>>t>>score>>src>>j>>di;P p;while(in>>v)p.push_back(v);paths[rank].push_back(p);}
 ifstream info("branches.txt");int rank,ep,y,nb,nf;while(info>>rank>>ep>>y>>nb>>nf){
  Search e;e.id=rank;int v;Mask F{};while(nb--){info>>v;e.ban[v]=true;}while(nf--){info>>v;put(F,v);}
  vector<array<Slice,2>> slices;
  for(auto p:paths[rank]){auto q=p;reverse(q.begin(),q.end());slices.push_back({Slice(p),Slice(q)});}
  for(int i=0;i<(int)slices.size()&&!e.found;i++)for(int j=0;j<i&&!e.found;j++)for(int di=0;di<2;di++)for(int dj=0;dj<2;dj++){
   auto&a=slices[i][di];auto&b=slices[j][dj];Mask force{};for(int t=0;t<8;t++)force[t]=F[t]&a.s.back()[t]&b.s.back()[t];put(force,ep);put(force,y);
   e.host1=a.s.back();e.host2=b.s.back();e.sa=i;e.sb=j;e.orient1=di;e.orient2=dj;
   for(int u=22;u<=172&&!e.found;u++)for(int h=max(22,170-u);h<=min(172,197-u)&&!e.found;h++){
    e.tried++;if(intersects(a.s[u],b.s[h])||intersects(a.n[u],b.s[h])||intersects(b.n[h],a.s[u])||!covers(a.s[u],b.s[h],force))continue;
    e.valid++;e.a.assign(a.p.begin(),a.p.begin()+u);e.b.assign(b.p.begin(),b.p.begin()+h);for(int v:e.a)e.setv(v,1);for(int v:e.b)e.setv(v,1);
    e.bridge(e.a.back(),18);for(int v:e.b)e.setv(v,-1);for(int v:e.a)e.setv(v,-1);
   }
  }cout<<"DONE "<<rank<<" "<<e.tried<<" "<<e.valid<<" "<<e.bridges<<" "<<e.calls<<" "<<e.tips<<" "<<e.maxlen<<endl;if(e.found)return 0;
 }
}
