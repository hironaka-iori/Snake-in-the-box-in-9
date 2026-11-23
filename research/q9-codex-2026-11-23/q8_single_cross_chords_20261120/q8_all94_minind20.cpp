#include<algorithm>
#include<array>
#include<bit>
#include<cassert>
#include<fstream>
#include<iostream>
#include<numeric>
#include<set>
#include<string>
#include<vector>
using namespace std;using P=vector<int>;using U=uint64_t;using M=array<U,4>;
struct Arm{P p;bool fresh;};struct Group{array<vector<U>,4>m;vector<Arm>arms;};
string canonical(const P&p){string best;for(int dir:{1,-1}){int ren[9];fill(ren,ren+9,-1);int cnt=0;string s;for(int k=1;k<p.size();k++){int i=dir>0?k:p.size()-k;int d=countr_zero(unsigned(p[i]^p[i-1]));if(ren[d]<0)ren[d]=cnt++;s+='0'+ren[d];}if(best.empty()||s<best)best=s;}return best;}
int main(int argc,char**argv){array<Group,100> all,fresh;set<string>known;string w;
for(int f=1;f<=2;f++){ifstream in(argv[f]);while(in>>w){if(w.size()<93||!known.insert(w).second)continue;P p{0};M m{};for(char d:w){int x=p.back()^1<<(d-'0');p.push_back(x);m[x>>6]|=1ull<<(x&63);}for(auto*g:{&all,&fresh}){if(g==&fresh&&f==1)continue;auto&z=(*g)[w.size()];z.arms.push_back({p,f==2});for(int i=0;i<4;i++)z.m[i].push_back(m[i]);}}}
int goal=stoi(argv[3]);long long total=0;set<string>classes;
for(int l=98;l>=(goal-1+1)/2;l--){int m=goal-1-l;array<int,8>perm;iota(perm.begin(),perm.end(),0);
long long attempts=0,matched=0,newMatched=0;int optimum=512;P example,newExample;
 do{int map[256]{};for(int v=1;v<256;v++)map[v]=map[v&(v-1)]^(1<<perm[countr_zero(unsigned(v))]);
 for(auto&b:all[l].arms){auto&g=all[m];M bm{};for(int i=1;i<b.p.size();i++){int x=map[b.p[i]];bm[x>>6]|=1ull<<(x&63);}attempts+=g.arms.size();
 const U *p0=g.m[0].data(),*p1=g.m[1].data(),*p2=g.m[2].data(),*p3=g.m[3].data();
 for(int i=0;i<g.arms.size();i++){int d=popcount(p0[i]&bm[0])+popcount(p1[i]&bm[1])+popcount(p2[i]&bm[2])+popcount(p3[i]&bm[3]);if(d>optimum)continue;
 if(d<optimum){optimum=d;matched=0;newMatched=0;example.clear();newExample.clear();}
 matched++;bool n=b.fresh||g.arms[i].fresh;
 if(n)newMatched++;
 if(example.empty()||(n&&newExample.empty())){P q(g.arms[i].p.rbegin(),g.arms[i].p.rend());for(int v:b.p)q.push_back(map[v]+256);
 if(example.empty())example=q;if(n&&newExample.empty())newExample=q;}
 }
 }}while(next_permutation(perm.begin(),perm.end()));
 total+=attempts;cout<<"MIN "<<goal<<" "<<l<<" "<<m<<" "<<optimum<<" "<<attempts<<" "<<matched<<" "<<newMatched<<endl;
 for(auto*ex:{&example,&newExample})if(!ex->empty()){cout<<(ex==&example?"WITNESS":"NEW_ARM_WITNESS");for(int v:*ex)cout<<" "<<v;cout<<endl;}
 }cout<<"TOTAL "<<goal<<" "<<total<<endl;}
