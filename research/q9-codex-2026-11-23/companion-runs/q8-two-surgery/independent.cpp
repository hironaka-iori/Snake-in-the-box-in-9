#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using T=array<P,3>;using M=array<uint64_t,4>;
int nb[256][8],occ[256],deg[256],pi[8],available=255,sec,cap,target,best=0;long long choices,nodes,answers=0;bool stopFlag=false;
P a,b,c,steps,append;set<M> seen;chrono::steady_clock::time_point start;
void mark(int x,int s){occ[x]=s>0;for(int y:nb[x])deg[y]+=s;}
void finalEmit(){M m{};for(auto*q:{&a,&c,&append})for(int x:*q)m[x/64]|=1ull<<(x%64);
 if(!seen.insert(m).second)return;int n=a.size()+append.size()+c.size();best=max(best,n);++answers;
 int z=a[0];cout<<a.size()+append.size();for(auto*q:{&a,&append})for(int v:*q)cout<<" "<<(v^z);cout<<" "<<c.size();for(int v:c)cout<<" "<<(v^z);cout<<endl;}
P otherArm,csteps;int mapping[8],freeAxes;long long built=0,packedNodes=0;using CacheKey=pair<M,P>;set<CacheKey> tried;
void pack(int v,int ix){++packedNodes;
 if(ix==csteps.size()){swap(c,otherArm);finalEmit();swap(c,otherArm);return;}
 int d=csteps[ix],opts=mapping[d]<0?freeAxes:1<<mapping[d];
 while(opts){int w=opts&-opts;opts^=w;int y=v^w;if(occ[y]||deg[y])continue;bool fresh=mapping[d]<0;if(fresh){mapping[d]=countr_zero((unsigned)w);freeAxes^=w;}otherArm.push_back(y);pack(y,ix+1);otherArm.pop_back();if(fresh){freeAxes^=w;mapping[d]=-1;}}
}
void emit(){++built;M m{};for(auto*p:{&a,&append})for(int x:*p)m[x/64]|=1ull<<(x%64);if(tried.size()>2000000)tried.clear();if(!tried.insert({m,csteps}).second)return;
 for(int x:append)mark(x,1);fill(mapping,mapping+8,-1);freeAxes=255;for(int src=0;src<256;src++)if(!occ[src]&&!deg[src]){otherArm={src};pack(src,0);}for(int x:append)mark(x,-1);
}
void dfs(int v,int ix){++nodes;if(ix==steps.size()){emit();return;}
 int d=steps[ix],opts=pi[d]<0?available:1<<pi[d];while(opts){int w=opts&-opts;opts^=w;int y=v^w;if(occ[y]||deg[y])continue;bool fresh=pi[d]<0;if(fresh){pi[d]=countr_zero((unsigned)w);available^=w;}append.push_back(y);dfs(y,ix+1);append.pop_back();if(fresh){available^=w;pi[d]=-1;}}
}
int main(int argc,char**argv){if(argc!=4)return 3;target=atoi(argv[1]);cap=atoi(argv[2]);sec=atoi(argv[3]);for(int x=0;x<256;x++)for(int d=0;d<8;d++)nb[x][d]=x^(1<<d);start=chrono::steady_clock::now();string line;vector<T>ds;
 while(getline(cin,line)){istringstream in(line);T t;int n,v;for(auto&p:t){in>>n;while(n--){in>>v;p.push_back(v);}}ds.push_back(t);}
 for(int k=0;k<=cap;k++)for(auto&raw:ds)for(int fixed=0;fixed<3;fixed++)for(int moving=0;moving<3;moving++)if(fixed!=moving){
 int standing=3-moving-fixed;for(int dir=0;dir<4;dir++){a=raw[standing];b=raw[moving];c=raw[fixed];if(dir&1)reverse(a.begin(),a.end());if(dir&2)reverse(b.begin(),b.end());
 for(int ra=0;ra<=k;ra++){int rb=k-ra;if(ra>=a.size()||rb>=b.size())continue;int n=a.size()+b.size()+c.size()-k;if(n<target||a.size()+b.size()-k<50||c.size()<2)continue;csteps.clear();for(int h=1;h<c.size();h++)csteps.push_back(countr_zero(unsigned(c[h]^c[h-1])));
 P ta(a.end()-ra,a.end());a.resize(a.size()-ra);for(int x:a)mark(x,1);steps.clear();for(int i=rb+1;i<b.size();i++)steps.push_back(countr_zero(unsigned(b[i]^b[i-1])));
 fill(pi,pi+8,-1);for(int src:nb[a.back()])if(!occ[src]&&deg[src]==1){++choices;append={src};dfs(src,0);}
 for(int x:a)mark(x,-1);a.insert(a.end(),ta.begin(),ta.end());if(chrono::duration<double>(chrono::steady_clock::now()-start).count()>=sec)goto done;
 }}}
 done:cerr<<"donors "<<ds.size()<<" anchored placements "<<choices<<" permuted nodes "<<nodes<<" formed joined arms "<<built<<" third arm nodes "<<packedNodes<<" saved "<<answers<<" best "<<best<<endl;
}

