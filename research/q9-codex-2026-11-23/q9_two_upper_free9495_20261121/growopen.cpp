#include <random>
#include <numeric>
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
 array<int,8> order{0,1,2,3,4,5,6,7};
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
  P&arm=left?a:b;int v=arm.back();for(int i=0;i<8&&nodes<=budget&&best<goal;i++){int x=v^1<<order[i];if(used[x]||d->banned[x]||near[x]!=1)continue;mark(x,1);arm.push_back(x);dfs(left);arm.pop_back();mark(x,-1);}
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
 ifstream ins("survey.seeds");struct Seed{int n,id;P a,b;};vector<Seed> ss;int id,len,na,nb;while(ins>>id>>len>>na){P a(na);for(int&v:a)ins>>v;ins>>nb;P b(nb);for(int&v:b)ins>>v;if(id>=16&&id<(int)ds.size()&&id!=16&&id!=50&&id!=100&&id!=1629&&id!=4000&&id!=3050&&id!=4681)ss.push_back({len,id,a,b});}
 sort(ss.begin(),ss.end(),[](const Seed&a,const Seed&b){return a.n!=b.n?a.n>b.n:a.id<b.id;});mt19937 rng(9151121);int visited=0;
 ofstream stat(prefix+".stats");for(const auto& p:ss){if(visited>=threshold)break;visited++;r.d=&ds[p.id];long long calls0=r.cnt.calls;int prev=r.cnt.best;r.cnt.best=0;
   for(int t=0;t<stride;t++){shuffle(r.order.begin(),r.order.end(),rng);int x=t?int(rng()%release):0,y=t?int(rng()%release):0;
    int n=max(1,(int)p.a.size()-x),m=max(1,(int)p.b.size()-y); if(t%2){reverse(r.d->low.begin(),r.d->low.end());r.search(p.b,m,p.a,n);reverse(r.d->low.begin(),r.d->low.end());}else r.search(p.a,n,p.b,m);
    if(r.best>=192)break;
   }
   stat<<p.id<<" "<<p.n<<" "<<r.cnt.best<<" "<<r.cnt.calls-calls0<<endl;r.cnt.best=max(prev,r.cnt.best);if(r.best>=192)break;
 }
 done:cout<<"DONE "<<ds.size()<<" "<<r.cnt.tries<<" "<<r.cnt.passes<<" "<<r.cnt.sets<<" "<<r.cnt.calls<<" "<<r.cnt.caps<<" "<<r.best<<endl;
}
