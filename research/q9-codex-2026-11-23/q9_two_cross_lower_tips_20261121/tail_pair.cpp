#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Mask=array<unsigned long long,4>;
void mark(Mask&m,int v){m[v/64]|=1ULL<<(v%64);}
bool common(const Mask&a,const Mask&b){return ((a[0]&b[0])|(a[1]&b[1])|(a[2]&b[2])|(a[3]&b[3]))!=0;}
using Duo=array<vector<int>,2>; struct Tail{Mask mask{};vector<int> walk;};
array<int,256>deny{},endBad{};vector<int>active;int need,cap;bool upper,truncated;long long ticks,limit;vector<Tail>found;unsigned st=192177315;unsigned random32(){st^=st<<13;st^=st>>17;return st^=st<<5;}
void neighborhood(int x,int delta){deny[x]+=delta;for(int d=0;d<8;d++)deny[x^(1<<d)]+=delta;}
void enumerate(int v){
 if(truncated)return;if(++ticks>limit){truncated=true;return;}
 if(active.size()==need){if(!upper||!endBad[v]){Tail t;t.walk=active;for(auto x:active)mark(t.mask,x);if(upper){mark(t.mask,v);for(int d=0;d<8;d++)mark(t.mask,v^(1<<d));}found.push_back(move(t));if(found.size()>=cap)truncated=true;}return;}
 int options[8],n=0;for(int d=0;d<8;d++){int x=v^(1<<d);if(!deny[x])options[n++]=x;}neighborhood(v,1);
 for(int j=n-1;j>=0&&!truncated;j--){int k=random32()%(j+1),x=options[k];swap(options[k],options[j]);active.push_back(x);enumerate(x);active.pop_back();}neighborhood(v,-1);
}
vector<Tail> gen(const Duo&p,int side,int len){
 upper=side;const auto&a=p[side];const auto&b=p[1-side];deny.fill(0);endBad.fill(0);for(int i=1;i<b.size();i++)deny[b[i]]++;
 if(upper)for(int x:b){endBad[x]++;for(int d=0;d<8;d++)endBad[x^(1<<d)]++;}
 for(int i=0;i+1<a.size();i++)neighborhood(a[i],1);
 need=len-a.size();assert(need>0);active.clear();found.clear();truncated=false;ticks=0;enumerate(a.back());return move(found);
}
bool verify(const Duo&p){vector<int>z(p[0].rbegin(),p[0].rend());for(int v:p[1])z.push_back(256+v);z.push_back(p[1].back());for(int i=0;i<z.size();i++)for(int j=0;j<i;j++)if(z[j]==z[i]||((popcount(unsigned(z[j]^z[i]))==1)!=(j+1==i)))return false;return true;}
int main(int argc,char**argv){assert(argc==6);ifstream f(argv[1]);int n,m;vector<Duo>seeds;while(f>>n>>m){Duo p;p[0].resize(n);p[1].resize(m);for(auto&a:p)for(int&v:a)f>>v;seeds.push_back(p);}int rounds=stoi(argv[2]);limit=stoll(argv[3]);cap=stoi(argv[4]);int mode=stoi(argv[5]);int best=190,full=0,live=0,kept=0;long long allTicks=0,combos=0;set<Duo>cases;
 for(int j=0;j<rounds;j++){int id=j<600?j%min(int(seeds.size()),8):random32()%seeds.size();auto p=seeds[id];
 int k=4+random32()%42,l=4+random32()%42;int goalA=96,goalB=96;if(mode&&j%4==3){if(random32()&1)goalA--;else goalB--;}
 if(p[0].size()<goalA-k||p[1].size()<goalB-l)continue;
 p[0].resize(goalA-k);p[1].resize(goalB-l);if(!cases.insert(p).second)continue;
 Mask prefix{};for(int v:p[0])mark(prefix,v);bool good=true;for(int i=1;i<p[1].size();i++){Mask t{};mark(t,p[1][i]);if(common(t,prefix))good=false;}if(!good)continue;
 auto a=gen(p,0,goalA);bool all=!truncated;allTicks+=ticks;
 if(a.empty()){full+=all;continue;}
 auto b=gen(p,1,goalB);all&=!truncated;allTicks+=ticks;if(all)full++;if(b.empty())continue;live++;
 for(auto &bb:b)for(auto &aa:a){combos++;if(common(bb.mask,aa.mask))continue;auto out=p;out[0].insert(out[0].end(),aa.walk.begin(),aa.walk.end());out[1].insert(out[1].end(),bb.walk.begin(),bb.walk.end());assert(verify(out));kept++;
 if(goalA+goalB>best){best=goalA+goalB;cout<<"BEST "<<best<<" "<<id<<" "<<j<<" "<<goalA<<" "<<goalB;for(auto&v:out)for(int x:v)cout<<" "<<x;cout<<endl;if(best==192)return 0;}goto done;
 }done:;
 }cout<<"DONE "<<rounds<<" unique_prefix_pairs "<<cases.size()<<" exhaustive "<<full<<" both_tail_sets_nonempty "<<live<<" nodes "<<allTicks<<" pairs "<<combos<<" hits "<<kept<<" best "<<best<<endl;
}
