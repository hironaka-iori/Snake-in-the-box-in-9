#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;using P=vector<int>;using M=array<unsigned long long,4>;using SH=array<int,4>;
M nb[256];int bit(M a,int v){return (a[v>>6]>>(v&63))&1;}M minusN(M a,int v){for(int j=0;j<4;j++)a[j]&=~nb[v][j];return a;}
struct S{P anc,l,r;int L=93,pad;long long cap,nodes=0,checked=0,pruned=0,hit92=0,hit93=0;bool stop=false;int occ[256]{},deg[256]{};ofstream out;S(string f):out(f){}
void mark(int x,int d){occ[x]+=d;for(int j=0;j<8;j++)deg[x^1<<j]+=d;}
bool find3(const M& f,SH& res){
    for(int g=0;g<4;g++)for(auto w=f[g];w;w&=w-1){int b=64*g+countr_zero(w);int ds[8],n=0;for(int j=0;j<8;j++)if(bit(f,b^1<<j))ds[n++]=j;if(n<2)continue;
      for(int t=0;t<n;t++){int c=b^1<<ds[t];for(int h=0;h<8;h++){if(h==ds[t]||!bit(f,c^1<<h))continue;for(int k=0;k<n;k++)if(k!=t&&ds[k]!=h){res={b^1<<ds[k],b,c,c^1<<h};return true;}}}}
    return false;}
void rec(bool left,int steps,M free,SH s){
 if(nodes>=cap){stop=true;return;}nodes++;
 if(steps>=92){(steps==92?hit92:hit93)++;P p(l.rbegin(),l.rend());p.insert(p.end(),anc.begin(),anc.end());p.insert(p.end(),r.begin(),r.end());out<<p.size();for(int v:p)out<<" "<<v;out<<endl;if(steps==93)return;}
 if(left)rec(false,steps,free,s);P&arm=left?l:r;int tip=arm.empty()?(left?anc[0]:anc.back()):arm.back();for(int j=0;j<8&&!stop;j++){int v=tip^1<<j;if(occ[v]||deg[v]!=1)continue;
 M ff=minusN(free,v);SH sh=s;if(!bit(ff,s[0])||!bit(ff,s[1])||!bit(ff,s[2])||!bit(ff,s[3])){checked++;if(!find3(ff,sh)){pruned++;continue;}}
 mark(v,1);arm.push_back(v);rec(left,steps+1,ff,sh);arm.pop_back();mark(v,-1);}}
};
int main(int argc,char**argv){if(argc!=4)return 1;for(int v=0;v<256;v++){nb[v][v>>6]|=1ULL<<(v&63);for(int j=0;j<8;j++){int x=v^1<<j;nb[v][x>>6]|=1ULL<<(x&63);}}
ifstream f("inputs.dat");int id,n;f>>id>>n;P a(n);for(int&v:a)f>>v;int pad=atoi(argv[1]);S s(argv[3]);s.cap=atoll(argv[2]);s.anc=P(a.begin()+pad,a.end()-pad);M free;free.fill(~0ULL);for(int v:s.anc){s.mark(v,1);free=minusN(free,v);}SH sh;if(!s.find3(free,sh))return 2;s.rec(true,s.anc.size()-1,free,sh);cout<<"nodes "<<s.nodes<<" complete "<<!s.stop<<" geometry_checks "<<s.checked<<" pruned "<<s.pruned<<" raw92 "<<s.hit92<<" raw93 "<<s.hit93<<endl;
}
