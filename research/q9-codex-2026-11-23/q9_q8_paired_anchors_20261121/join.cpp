#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;using Mask=bitset<512>;
array<Mask,512> hood;mt19937 rng;struct Half{int lo,hi;string w;};
struct Path{string w;vector<int> vs;Mask forbidden;};
vector<string> mothers;vector<int> ids;array<vector<Half>,50> lefts,rights;long long tested=0,separated=0,bridges=0,calls=0,limited=0,compares=0;int budget,low=10000;ofstream record;string answer;
Path makepath(const string&s){Path h;h.w=s;h.vs={0};for(char c:s)h.vs.push_back(h.vs.back()^(1<<(c-'0')));for(int v:h.vs)h.forbidden|=hood[v];return h;}
void load(const char*fn,bool left){ifstream f(fn);int i,r,L,H,lo,hi,u,v;string m,w;array<set<string>,50>seen;while(f>>i>>r>>L>>H>>lo>>hi>>u>>v>>m>>w){if(u!=L||v!=H)continue;int ix=0;for(char c='0';c<='8';c++)if(m.find(c)==string::npos){m+=c;break;}for(char&c:w)c=char('0'+m.find(c));if(seen[i].insert(w).second)(left?lefts[i]:rights[i]).push_back({u,v,w});}}
int center,finalV;string gap,linkword;long long nodes;Mask goalblock,goalInner;
bool dfs(int v,int k,Mask active){
 if(nodes++>=budget)return false;++calls;
 if(k==(int)gap.size())return v==finalV;
 int req=gap[k]-'0';int remaining=((int)gap.size()-k)*2;if(popcount((unsigned)(v^finalV))>remaining)return false;
 for(int f=0;f<9;f++)if(f!=req)for(int a=0;a<2;a++){
 int d1=a?f:req,d2=a?req:f;int u=v^(1<<d1),y=u^(1<<d2);bool last=k+1==(int)gap.size();
 if(active[u]||active[y]||goalInner[u]||goalInner[y]&&(!last||y!=finalV)|| (last? (y!=finalV) : goalblock[y]))continue;
 if(!last&&goalblock[u])continue;
 if(last&&(hood[finalV][u]==0||y!=finalV))continue;
 linkword+=char('0'+d1);linkword+=char('0'+d2);if(dfs(y,k+1,active|hood[v]|hood[u]))return true;linkword.resize(linkword.size()-2);if(nodes>=budget)return false;
 }
 return false;
}
int countbad(const string &w){int f[512]={};int v=0;f[0]++;for(char c:w){v^=1<<(c-'0');f[v]++;}int cost=-int(w.size());for(int i=0;i<512;i++){cost+=f[i]*(f[i]-1)/2;for(int k=0;k<9;k++)if((i^(1<<k))>i)cost+=f[i]*f[i^(1<<k)];}return cost;}
int main(int argc,char**argv){if(argc!=5)return 2;int tests=stoi(argv[1]);budget=stoi(argv[2]);rng.seed(stoi(argv[3]));record.open(argv[4]);int i,r,z,t;string w;ifstream ma("mothers.tsv"),ce("centers.tsv");while(ma>>i>>r>>z>>t>>w)mothers.push_back(w);int b,o,m,s,n;while(ce>>b>>o>>m>>s>>n>>w)ids.push_back(m);
 for(int v=0;v<512;v++){hood[v].set(v);for(int k=0;k<9;k++)hood[v].set(v^(1<<k));}load("prefix.tsv",true);load("suffix.tsv",false);
 for(int i=0;i<(int)ids.size();i++){auto &ls=lefts[i],&rs=rights[i];if(ls.empty()||rs.empty())continue;for(int tr=0;tr<tests;tr++){
 auto &a=ls[rng()%ls.size()],&b=rs[rng()%rs.size()];int k=tr%7==0?0:(int)(rng()%23+1);int start=max(1,b.lo-k),end=min(a.hi,95-k);if(end<start)continue;int cut=start+rng()%(end-start+1),last=cut+k;
 auto p=makepath(a.w.substr(0,2*cut)),q=makepath(b.w.substr(2*(last-b.lo)));++compares;
 if(!k){string w=p.w+q.w;int cost=countbad(w);if(cost<low){low=cost;record<<"DIRECT "<<i<<' '<<cut<<' '<<cut<<' '<<cost<<' '<<w<<endl;}if(!cost)goto done;continue;}
 vector<int> dist;for(int d=0;d<512;d++)if((popcount((unsigned)d)%2)==0&&popcount((unsigned)d)<=2*k)dist.push_back(d);shuffle(dist.begin(),dist.end(),rng);
 for(int d:dist){int pos=p.vs.back()^d;++tested;
 bool ok=true;for(int x:q.vs)if(p.forbidden[x^pos]){ok=false;break;}if(!ok)continue;++separated;
 goalInner.reset();for(int j=1;j<(int)q.vs.size();j++)goalInner|=hood[q.vs[j]^pos];goalblock=goalInner|hood[pos];Mask block;for(int j=0;j+1<(int)p.vs.size();j++)block|=hood[p.vs[j]];
 gap=mothers[ids[i]].substr(cut,k);linkword.clear();nodes=0;finalV=pos;
 if(dfs(p.vs.back(),0,block)){string w=p.w+linkword+q.w;assert(countbad(w)==0);++bridges;record<<"FOUND "<<i<<' '<<cut<<' '<<last<<" 0 "<<w<<endl;goto done;}limited+=nodes>=budget;
 }
 }}
 done:cout<<"pair_trials "<<compares<<" placements "<<tested<<" disjoint_separated "<<separated<<" connector_nodes "<<calls<<" capped_connectors "<<limited<<" full_routes "<<bridges<<" best_fixed_seam_defects "<<low<<endl;
}
