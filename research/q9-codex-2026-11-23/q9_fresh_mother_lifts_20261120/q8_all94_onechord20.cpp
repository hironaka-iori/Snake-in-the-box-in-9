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
set<string>base,results; int goal=argc>3?stoi(argv[3]):192; long long tested=0,hits=0;
for(int l=98;l>=96;l--){int m=goal-1-l;array<int,8>perm; iota(perm.begin(),perm.end(),0);long long attempts=0,matches=0;
 do{int map[256]{};for(int v=1;v<256;v++)map[v]=map[v&(v-1)]^(1<<perm[countr_zero(unsigned(v))]);
 for(auto&b:all[l].arms){auto&g=b.fresh?all[m]:fresh[m];M bm{};for(int i=1;i<b.p.size();i++){int x=map[b.p[i]];bm[x>>6]|=1ull<<(x&63);}attempts+=g.arms.size();
 const U *p0=g.m[0].data(),*p1=g.m[1].data(),*p2=g.m[2].data(),*p3=g.m[3].data();
 for(int i=0;i<g.arms.size();i++){U a=p0[i]&bm[0];if(a&(a-1))continue;U c=p1[i]&bm[1];if((c&(c-1))||(a&&c))continue;U d=p2[i]&bm[2];if((d&(d-1))||((a|c)&&d))continue;U e=p3[i]&bm[3];if((e&(e-1))||((a|c|d)&&e))continue;
 int count=!!a+!!c+!!d+!!e;matches++;P q(g.arms[i].p.rbegin(),g.arms[i].p.rend());for(int v:b.p)q.push_back(256+map[v]);auto key=canonical(q);
 if(results.insert(key).second){cout<<"PATH "<<l<<" "<<m<<" "<<count;for(int v:q)cout<<" "<<v;cout<<endl;}
 }
 }}while(next_permutation(perm.begin(),perm.end()));hits+=matches;tested+=attempts;cerr<<"SPLIT "<<l<<"+"<<m<<" attempts "<<attempts<<" one_or_zero "<<matches<<endl;
}cerr<<"TOTAL "<<tested<<" one_or_zero "<<hits<<" distinct "<<results.size()<<endl;}
