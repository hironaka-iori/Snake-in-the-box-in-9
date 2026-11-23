#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;using P=vector<int>;using Mask=array<uint64_t,4>;using Perm=array<int,8>;
P makepath(const string&w,int v=0){P q{v};if(w!="-")for(char c:w)q.push_back(q.back()^(1<<(c-48)));return q;}
Mask mask(const P&p){Mask m{};for(int v:p)m[v>>6]|=uint64_t(1)<<(v&63);return m;}
bool hit(const Mask&a,const Mask&b){return (a[0]&b[0])||(a[1]&b[1])||(a[2]&b[2])||(a[3]&b[3]);}
struct Donor{int id,d;P low;Mask inner;array<bool,256>banned{};};
struct Count{long long tries=0,passes=0,sets=0,calls=0,caps=0;int best=0;};
struct Runner{
 Donor* d{};int budget=0,cap=0,goal=192,nodes;Count cnt;array<int,256>near{},used{};P a,b;int best=0;ofstream out;
 Runner(string file):out(file){}
 void mark(int x,int s){used[x]+=s;for(int i=0;i<8;i++)near[x^1<<i]+=s;}
 void take(){
  int n=d->low.size()+a.size()+b.size()-1;cnt.best=max(cnt.best,n);
  if(n<=best)return;best=n;P path;for(auto i=a.rbegin();i!=a.rend();i++)path.push_back(256+*i);path.insert(path.end(),d->low.begin(),d->low.end());for(int v:b)path.push_back(256+v);
  for(int j=0;j<(int)path.size();j++)for(int i=0;i<j;i++)if(path[i]==path[j]||(popcount(unsigned(path[i]^path[j]))==1)!=(j==i+1))abort();
  out<<n<<" "<<d->id;for(int z:path)out<<" "<<z;out<<endl;if(n>=192)cout<<"FOUND192 "<<d->id<<endl;
 }
 void dfs(bool left){
  if(++nodes>budget||best>=goal)return;cnt.calls++;take();if(best>=goal)return;if(left)dfs(false);
  P&arm=left?a:b;int v=arm.back();for(int i=0;i<8&&nodes<=budget&&best<goal;i++){int x=v^1<<i;if(used[x]||d->banned[x]||near[x]!=1)continue;mark(x,1);arm.push_back(x);dfs(left);arm.pop_back();mark(x,-1);}
 }
 void search(const P&A,int n,const P&B,int m){
  if(best>=goal)return;a.assign(A.begin(),A.begin()+n);b.assign(B.begin(),B.begin()+m);
  for(int v:a)mark(v,1);for(int v:b)mark(v,1);nodes=0;cnt.sets++;dfs(true);cnt.caps+=nodes>budget;for(int v:a)mark(v,-1);for(int v:b)mark(v,-1);
 }
};
int main(int argc,char**argv){
 if(argc!=8)return 2;string mode=argv[1],prefix=argv[7];int maxdonor=stoi(argv[2]),threshold=stoi(argv[3]),release=stoi(argv[4]),budget=stoi(argv[5]),stride=stoi(argv[6]);
 ifstream df("donors.words");string w;vector<Donor>ds;while(df>>w){P p=makepath(w);int delta=p.back();vector<int>b;for(int val:{1,0})for(int i=0;i<8;i++)if(((delta>>i)&1)==val)b.push_back(i);
  P q;for(int x:p){int t=0;for(int i=0;i<8;i++)t|=((x>>b[i])&1)<<i;q.push_back(t);}Donor d{int(ds.size()),popcount(unsigned(delta)),q,mask(P(q.begin()+1,q.end()-1))};
  for(int j=1;j+1<(int)q.size();j++)d.banned[q[j]]=true;ds.push_back(d);if(int(ds.size())>=maxdonor)break;}
 Runner r(prefix+".paths");r.budget=budget;if(mode=="control")r.goal=190;
 if(mode=="direct"||mode=="control"){
  // Align direct arms to the same normalized lower coordinate order.
  ifstream orig("donors.words");vector<string>words;while(orig>>w)words.push_back(w);ifstream f("direct.dat");int i;string u,v;
  struct A{P a,b;};vector<vector<A>>banks(ds.size());while(f>>i>>u>>v){if(i>=(int)ds.size())continue;P ref=makepath(words[i]);int dx=ref.back();P ar=makepath(u),br=makepath(v,dx);vector<int>perm;for(int val:{1,0})for(int b=0;b<8;b++)if(((dx>>b)&1)==val)perm.push_back(b);
   for(P*q:{&ar,&br})for(int&z:*q){int t=0;for(int b=0;b<8;b++)t|=((z>>perm[b])&1)<<b;z=t;}banks[i].push_back({ar,br});}
  for(auto&d:ds){r.d=&d;for(auto&u:banks[d.id])for(auto&v:banks[d.id]){
    for(int x=0;x<=release&&int(u.a.size())>x;x+=2)for(int y=0;y<=release&&int(v.b.size())>y;y+=2){
     if(mode=="control"&&(x<2||y<2))continue;P a(u.a.begin(),u.a.end()-x),b(v.b.begin(),v.b.end()-y);Mask forbid=mask(b);for(int w:b)for(int j=0;j<8;j++){int v=w^1<<j;forbid[v>>6]|=1ULL<<(v&63);}
     r.cnt.tries++;if(hit(mask(a),forbid))continue;r.cnt.passes++;r.search(a,a.size(),b,b.size());if(r.best>=r.goal)goto done;
   }}}
 }else{
  struct F{int d;P a,b;};vector<F>fs;ifstream f("forests.dat");int d,m,ix,ax,z;string a,b;
  while(f>>d>>a>>b>>m>>ix>>ax>>z){P aa=makepath(a),bb=makepath(b,(1<<d)-1);fs.push_back({d,aa,bb});}
  for(int dim=1;dim<=8;dim++){vector<Donor*> candidates;for(auto&d:ds)if(d.d==dim)candidates.push_back(&d);if(candidates.empty())continue;
   Perm p={0,1,2,3,4,5,6,7};int permid=0;
   do{do{if(permid++%stride)continue;array<int,256>map{};for(int k=1;k<256;k++)map[k]=map[k&(k-1)]^1<<p[countr_zero((unsigned)k)];
      for(auto&g:fs)if(g.d==dim){P u,v;for(int x:g.a)u.push_back(map[x]);for(int x:g.b)v.push_back(map[x]);
       int keepa=max(1,int(u.size())-release),keepb=max(1,int(v.size())-release);Mask need=mask(P(u.begin(),u.begin()+keepa));auto mm=mask(P(v.begin(),v.begin()+keepb));for(int i=0;i<4;i++)need[i]|=mm[i];
       for(auto d:candidates){r.cnt.tries++;if(hit(need,d->inner))continue;int na=0,nb=0;while(na<(int)u.size()&&!d->banned[u[na]])na++;while(nb<(int)v.size()&&!d->banned[v[nb]])nb++;
        if(int(d->low.size())+na+nb-1<threshold)continue;r.d=d;r.cnt.passes++;
        for(int x:{0,2,5})for(int y:{0,2,5})if(na>x&&nb>y){r.search(u,na-x,v,nb-y);if(r.best>=r.goal)goto done;}
       }
      }
   }while(next_permutation(p.begin()+dim,p.end()));}while(next_permutation(p.begin(),p.begin()+dim));
  }
 }
 done:cout<<"DONE "<<ds.size()<<" "<<r.cnt.tries<<" "<<r.cnt.passes<<" "<<r.cnt.sets<<" "<<r.cnt.calls<<" "<<r.cnt.caps<<" "<<r.best<<endl;
}
