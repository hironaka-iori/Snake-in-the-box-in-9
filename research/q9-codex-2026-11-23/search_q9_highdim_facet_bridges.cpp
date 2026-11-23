// Retain disjoint long Q9 segments and enumerate short chordless paths between their chosen tips.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
using P=vector<int>;using Bank=vector<P>;
struct Engine{
 Bank parts;int goal,lim,bridgecap,k;long long nodes=0,joins=0,endnodes=0;vector<vector<Bank>>between;array<int,512>owner{},fixedNbr{},temp{};P w;mt19937&rng;P answer;int best=0;
 int tip(int port){auto&q=parts[port/2];return port%2?q.back():q.front();}
 Engine(Bank v,int g,int l,int c,mt19937&r):parts(move(v)),goal(g),lim(l),bridgecap(c),k(parts.size()),between(2*k,vector<Bank>(2*k)),rng(r){
  owner.fill(-1);for(int b=0;b<k;b++)for(int x:parts[b]){owner[x]=b;for(int d=0;d<9;d++)fixedNbr[x^1<<d]++;}
 }
 void mark(int x,int sign){temp[x]+=10*sign;for(int d=0;d<9;d++)temp[x^1<<d]+=sign;}
 void findlinks(int a,int b,int x,P&path,int&used){
  if(used++>=bridgecap||(int)between[a][b].size()>=60)return;nodes++;
  int start=tip(a),end=tip(b);int dist=popcount((unsigned)(x^end));if(dist>lim+1-(int)path.size())return;
  for(int d=0;d<9;d++){int z=x^1<<d;if(owner[z]>=0||temp[z]!=(path.empty()?0:1))continue;
   bool hitsend=popcount((unsigned)(z^end))==1;if(fixedNbr[z]!=(int)hitsend+int(path.empty()))continue;
   // A later connector point must not touch its starting port.
   if(!path.empty()&&popcount((unsigned)(z^start))==1)continue;
   path.push_back(z);if(hitsend){between[a][b].push_back(path);between[b][a].emplace_back(path.rbegin(),path.rend());}
   else if((int)path.size()<lim){mark(z,1);findlinks(a,b,z,path,used);mark(z,-1);}path.pop_back();
  }
 }
 bool valid(const P&p){for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||(popcount((unsigned)(p[i]^p[j]))==1)!=(i==j+1))return false;return true;}
 bool extend(P&p,int side,int&budget){
  if(++budget>18000)return false;endnodes++;if((int)p.size()>best){if(!valid(p))abort();best=p.size();answer=p;}
  if((int)p.size()>goal)return true;
  int t=side?p.back():p.front();for(int d=0;d<9;d++){int z=t^1<<d;if(temp[z]!=1)continue;
   if(side)p.push_back(z);else p.insert(p.begin(),z);mark(z,1);if(extend(p,side,budget))return true;mark(z,-1);if(side)p.pop_back();else p.erase(p.begin());}
  return !side&&extend(p,1,budget);
 }
 bool assemble(int port,int mask,P&p){
  if(mask+1==1<<k){joins++;if(!valid(p))abort();auto saved=temp;temp.fill(0);for(int x:p)mark(x,1);int b=0;bool ok=extend(p,0,b);temp=saved;return ok;}
  for(int b=0;b<2*k;b++)if(!(mask>>int(b/2)&1))for(auto&link:between[port][b]){
   bool ok=true;for(int v:link)if(temp[v]){ok=false;break;}if(!ok)continue;
   int old=p.size();for(int z:link){p.push_back(z);mark(z,1);}auto&q=parts[b/2];if(b%2)p.insert(p.end(),q.rbegin(),q.rend());else p.insert(p.end(),q.begin(),q.end());
   if(assemble(b^1,mask|1<<(b/2),p))return true;p.resize(old);for(int z:link)mark(z,-1);
  }return false;
 }
 bool run(){
  for(int a=0;a<2*k;a++)for(int b=a+1;b<2*k;b++)if(a/2!=b/2){int u=0;P h;findlinks(a,b,tip(a),h,u);}
  for(int a=0;a<2*k;a++){P p=parts[a/2];if(a%2)reverse(p.begin(),p.end());if(assemble(a^1,1<<(a/2),p))return true;}return false;
 }
};
int main(int argc,char**argv){
 if(argc!=7)return 2;int goal=stoi(argv[1]),rounds=stoi(argv[2]),gap=stoi(argv[3]),budget=stoi(argv[4]),trim=stoi(argv[5]);mt19937 rng(stoul(argv[6]));vector<Bank>banks;string line;
 while(getline(cin,line)){istringstream ss(line);int n,x;Bank b;while(ss>>n){P p;for(int i=0;i<n;i++){ss>>x;p.push_back(x);}b.push_back(p);}if(!b.empty())banks.push_back(b);}
 long long nodes=0,joins=0,extra=0;int best=0;for(int r=0;r<rounds;r++){auto parts=banks[r<banks.size()?r:rng()%banks.size()];
  if(r>=(int)banks.size()){if(parts.size()>1&&rng()%3==0)parts.resize(1+rng()%parts.size());for(auto&p:parts){
   int front=min((int)p.size()-1,(int)(rng()%(1+trim)));if(rng()%3==0)front=0;
   int back=min((int)p.size()-1-front,(int)(rng()%(1+trim)));if(rng()%3==0)back=0;p= P(p.begin()+front,p.end()-back);
  }}
  int n=0;for(auto&p:parts)n+=p.size();if(n<140)continue;Engine e(parts,goal,gap,budget,rng);bool found=e.run();nodes+=e.nodes;joins+=e.joins;extra+=e.endnodes;
  if(e.best>best){best=e.best;cout<<"BEST "<<best-1<<" trial "<<r<<" vertices";for(int x:e.answer)cout<<" "<<x;cout<<endl;}
  if(found)return 0;if((r+1)%2000==0)cout<<"progress "<<r+1<<" best "<<best-1<<" bridge_nodes "<<nodes<<" assemblies "<<joins<<" end_nodes "<<extra<<endl;
 }cout<<"DONE "<<rounds<<" best "<<best-1<<" bridge_nodes "<<nodes<<" assemblies "<<joins<<" end_nodes "<<extra<<endl;
}
