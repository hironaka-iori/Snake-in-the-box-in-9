#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using T=chrono::steady_clock;int nb[512][9];int occ[512],deg[512],target=191,nodecap,id,cutl,cutr,control;unsigned long long nodes=0,all=0,capped=0,jobs=0;int best=0;bool hit=0;set<string>known,found190;ofstream labels;P lefttip,righttip,core;mt19937 gen;array<int,9>dirs;
void mark(int x,int s){occ[x]+=s;for(int y:nb[x])deg[y]+=s;}
string key(P q){string ans;for(int dir:{1,-1}){int m[9]{},h=0;string k;for(int i=1;i<q.size();i++){int d=countr_zero(unsigned(q[i]^q[i-1]));if(!m[d])m[d]=++h;k+=char('0'+m[d]-1);}if(ans.empty()||k<ans)ans=k;reverse(q.begin(),q.end());}return ans;}
bool valid(P const&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));if(i==j+1?d!=1:d<2)return false;}return true;}
void check(int n){best=max(best,n-1);if(n<191)return;P q(lefttip.rbegin(),lefttip.rend());q.insert(q.end(),core.begin(),core.end());q.insert(q.end(),righttip.begin(),righttip.end());if(n==191){auto k=key(q);if(!known.count(k)&&found190.insert(k).second){if(!valid(q))abort();labels<<id<<" "<<cutl<<" "<<cutr;for(int v:q)labels<<" "<<v;labels<<endl;}return;}if(!valid(q))abort();cout<<id<<" "<<cutl<<" "<<cutr;for(int v:q)cout<<" "<<v;cout<<endl;hit=true;}
void grow(int side,int n){if(hit||++nodes>nodecap)return;++all;check(n);if(hit)return;if(!side)grow(1,n);auto&arm=side?righttip:lefttip;int end=arm.empty()?(side?core.back():core.front()):arm.back();for(int d:dirs){int v=nb[end][d];if(occ[v]||deg[v]!=1)continue;arm.push_back(v);mark(v,1);grow(side,n+1);mark(v,-1);arm.pop_back();if(hit||nodes>nodecap)break;}}
struct Seed{int a,L;P p;};int main(int argc,char**argv){if(argc!=7)return 1;ifstream f(argv[1]);string word;while(f>>word)known.insert(word);labels.open(argv[2]);int secs=atoi(argv[3]);nodecap=atoi(argv[4]);int maxcut=atoi(argv[5]);control=atoi(argv[6]);gen.seed(92647);iota(dirs.begin(),dirs.end(),0);for(int x=0;x<512;x++)for(int d=0;d<9;d++)nb[x][d]=x^(1<<d);vector<Seed>seeds;string line;while(getline(cin,line)){istringstream in(line);Seed s;in>>s.a>>s.L;int v;while(in>>v)s.p.push_back(v);if(!valid(s.p))abort();seeds.push_back(s);}
 auto start=T::now();int passes=0;for(int k=0;k<=maxcut;k++){for(id=0;id<seeds.size();id++){auto&s=seeds[id];for(int l=0;l<=k;l++){cutl=l;cutr=k-l;if(cutl>s.a||s.p.size()-cutr<s.a+s.L)continue;core={s.p.begin()+l,s.p.end()-cutr};for(int x:core)mark(x,1);nodes=0;shuffle(dirs.begin(),dirs.end(),gen);++jobs;grow(0,core.size());if(nodes>nodecap)capped++;for(int x:core)mark(x,-1);if(hit){if(!control)goto done;hit=false;goto nextSeed;}if(!(jobs%1024)&&chrono::duration<double>(T::now()-start).count()>=secs)goto done;}nextSeed:;}passes++;}
 done:cerr<<"seeds "<<seeds.size()<<" completed_cut_levels "<<passes<<" jobs "<<jobs<<" cap "<<capped<<" nodes "<<all<<" max "<<best<<" new_to_190_baseline "<<found190.size()<<endl;}

