#include <array>
#include <algorithm>
#include <bit>
#include <iostream>
#include <vector>
using namespace std;
struct Way {array<unsigned short,9> v{};};struct Gap {int h=0;vector<Way> opt;};
struct Search{
 array<int,512> oc{},nb{},ban{};vector<Gap> g;vector<int> order;int cap=1000,lim=2000,used=0;bool exceeded=false;
 void ways(Gap&g,int a,int b,int x,int idx,Way&q){
  if(g.opt.size()>cap)return;
  int z=x^b;if(has_single_bit(unsigned(z))){g.opt.push_back(q);return;}
  for(;z;z&=z-1){int y=x^(z&-z);if(oc[y]||nb[y]!=has_single_bit(unsigned(y^a))+has_single_bit(unsigned(y^b)))continue;
   q.v[idx]=y;ways(g,a,b,y,idx+1,q);}
 }
 bool fit(const Gap&g,const Way&o){for(int i=0;i<g.h-1;++i)if(ban[o.v[i]])return false;return true;}
 void put(const Gap&g,const Way&o,int d){for(int i=0;i<g.h-1;++i){int x=o.v[i];ban[x]+=d;for(int j=0;j<9;++j)ban[x^(1<<j)]+=d;}}
 bool go(int pos,int skips){
  if(++used>lim){exceeded=true;return false;}if(order.size()-pos<=skips)return true;
  int best=-1,count=10000000,zero=0;
  for(int i=pos;i<order.size();++i){
   auto &a=g[order[i]];int n=0;
   for(auto &q:a.opt)if(fit(a,q)&&++n>=max(1,count))break;
   if(!n)++zero;
   if(n<count){count=n;best=i;}
   if(zero>skips)return false;
  }
  swap(order[pos],order[best]);auto &a=g[order[pos]];bool ok=false;
  for(auto&q:a.opt)if(fit(a,q)){
   put(a,q,1);ok=go(pos+1,skips);put(a,q,-1);if(ok||exceeded)break;
  }
  if(!ok&&!exceeded&&skips)ok=go(pos+1,skips-1);
  swap(order[pos],order[best]);return ok;
 }
 int run(const vector<int>&p){
  for(int x:p){oc[x]=1;for(int j=0;j<9;++j)nb[x^(1<<j)]++;}
  for(int i=0;i+1<p.size();++i){int a=p[i],b=p[i+1];if(has_single_bit(unsigned(a^b)))continue;
   Gap var;var.h=popcount(unsigned(a^b));Way tmp;ways(var,a,b,a,0,tmp);if(var.opt.size()<=cap)g.push_back(move(var));
  }
  for(int i=0;i<g.size();++i)order.push_back(i);
  sort(order.begin(),order.end(),[&](int a,int b){return g[a].opt.size()<g[b].opt.size();});bool sat=go(0,2);return exceeded?2:sat?1:0;
 }
};
int main(int argc,char**argv){int id,n;while(cin>>id>>n){vector<int>p{0};for(int i=0;i<n;++i){int m;cin>>m;p.push_back(p.back()^m);}
 Search s;s.cap=stoi(argv[1]);s.lim=stoi(argv[2]);int st=s.run(p);cout<<id<<" "<<st<<" "<<s.g.size()<<" "<<s.used<<endl;}}
