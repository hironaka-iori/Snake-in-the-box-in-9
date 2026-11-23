// Mutate the occupancy of a small Q8 face, retaining exactly two induced path components.
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using U=uint64_t;using Mask=array<U,4>;using Paths=vector<P>;
bool has(const Mask&s,int v){return s[v/64]>>(v%64)&1;}
void flip(Mask&s,int v){s[v/64]^=1ULL<<(v%64);}
struct Pit{Mask on{};array<int,256>degree{};int n=0,e=0;
 void toggle(int v){bool remove=has(on,v);int d=remove?-1:1;e+=d*degree[v];n+=d;flip(on,v);for(int a=0;a<8;a++)degree[v^1<<a]+=d;}
 Paths get(bool only=false)const{Paths out;Mask seen{};int count=0;for(int v=0;v<256;v++)if(has(on,v)&&degree[v]<=1&&!has(seen,v)){
   P w;int x=v,prev=-1;while(x>=0){if(has(seen,x))return {};flip(seen,x);count++;w.push_back(x);int next=-1;for(int d=0;d<8;d++){int z=x^1<<d;if(z!=prev&&has(on,z)){if(next>=0)return {};next=z;}}prev=x;x=next;}out.push_back(w);
  }if(count!=n||out.empty()||(only&&out.size()!=2))return {};return out;}
};
struct Face{P v;vector<P> patterns;};
vector<Face> make(int k){vector<Face>out;for(int mask=0;mask<256;mask++)if(popcount((unsigned)mask)==k){
 P sub{0};for(int d=0;d<8;d++)if(mask>>d&1){int n=sub.size();for(int j=0;j<n;j++)sub.push_back(sub[j]^1<<d);}
 for(int root=0;root<256;root++)if((root&mask)==0){Face f;for(int z:sub)f.v.push_back(z^root);out.push_back(f);}
 }return out;}
int main(int argc,char**argv){
 if(argc!=6)return 2;int tries=stoi(argv[1]),minimum=stoi(argv[2]),limit=stoi(argv[3]),seed=stoi(argv[4]),temperature=stoi(argv[5]);mt19937 rng(seed);
 vector<Pit>base;string line;while(getline(cin,line)){istringstream in(line);int n,x;Pit p;while(in>>n){for(int j=0;j<n;j++){in>>x;if(has(p.on,x))abort();p.toggle(x);}}if(!p.get().empty())base.push_back(p);}
 if(base.empty())return 3;auto faces=make(2);auto f3=make(3);faces.insert(faces.end(),f3.begin(),f3.end());
 vector<Pit>bank=base;set<Mask>seen;int emitted=0,best=0;long long legal=0;
 auto emit=[&](const Pit&p,const Paths&w){if(w.size()!=2||p.n<minimum||!seen.insert(p.on).second)return;
  if(++emitted>limit)return;int shift=w[0][0];for(auto&a:w){cout<<a.size();for(int x:a)cout<<" "<<(x^shift);cout<<" ";}cout<<"\n";if(emitted%50==0)cout.flush();};
 for(auto&p:base){emit(p,p.get());best=max(best,p.n);}
 Pit cur=bank[rng()%bank.size()];for(int it=0;it<tries&&emitted<limit;it++){
  if(it%1500==0)cur=bank[rng()%bank.size()];auto &face=faces[rng()%faces.size()].v;int n=face.size(),old=0;for(int i=0;i<n;i++)if(has(cur.on,face[i]))old|=1<<i;
  for(int k=0;k<(n==4?8:17);k++){int pat=rng()%(1<<n);if(old==pat)continue;int gain=popcount((unsigned)pat)-popcount((unsigned)old);
   if(cur.n+gain<minimum-4||(!gain&&rng()%4==0))continue;
   if(gain < -2)continue; int oldK=cur.n-cur.e;
   int diff=old^pat;for(int m=diff;m;m&=m-1)cur.toggle(face[countr_zero((unsigned)m)]);
   int newK=cur.n-cur.e; bool ok=newK>=1&&newK<=7; int advantage=10*gain-16*(newK-oldK); if(advantage<0&&rng()%1000>1000*exp(advantage/(5.5+temperature*.06)))ok=false;for(int b=diff;ok&&b;b&=b-1){int v=face[countr_zero((unsigned)b)];
    if(has(cur.on,v)&&cur.degree[v]>2)ok=false;for(int d=0;ok&&d<8;d++){int x=v^1<<d;if(has(cur.on,x)&&cur.degree[x]>2)ok=false;}}
   Paths w;if(ok)w=cur.get();if(!w.empty()){legal++;best=max(best,cur.n);bool fresh=w.size()==2&&cur.n>=minimum&&!seen.count(cur.on);emit(cur,w);
    if(fresh||(newK<=4 && cur.n>=minimum-2+(newK-2) && rng()%35==0)){if(bank.size()<6000)bank.push_back(cur);else if(rng()%7==0)bank[rng()%bank.size()]=cur;}break;
   }for(int m=diff;m;m&=m-1)cur.toggle(face[countr_zero((unsigned)m)]);
  }
 }cerr<<"proposals "<<tries<<" moves "<<legal<<" emitted "<<emitted<<" bestQ8vertices "<<best<<" bank "<<bank.size()<<endl;
}
