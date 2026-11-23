#define main spectral_unused_main
#include "spectrum.cpp"
#undef main
#include <tuple>
struct Parent{array<P,2> h{};};
int main(int argc,char**argv){if(argc<3)return 1;ifstream in(argv[1]);vector<Parent> bank;string l;while(getline(in,l)){istringstream s(l);int id,k,d,z;s>>id>>k>>d;Parent p;while(s>>z)p.h[z/256][(z%256)/64]|=1ull<<(z%64);bank.push_back(p);}
 vector<array<int,7>> ranked;set<array<P,2>>seen;
 for(int j=2;j<argc;j++){ifstream in(argv[j]);int ix=0;while(getline(in,l)){istringstream ss(l);int a,b,m,v;if(!(ss>>a>>b>>m>>v))continue;int top=10000,fff=0,nv=0,errs=0;
 for(int flip=0;flip<2;flip++){auto h=bank[a].h;for(int x=v;x<256;x++)if((x&m)==v){int i=x/64;auto bit=1ull<<(x%64);for(int o=0;o<2;o++)h[o][i]=(h[o][i]&~bit)|(bank[b].h[o^flip][i]&bit);}
 auto on=[&](int x){return h[x/256][(x%256)/64]>>(x%64)&1;};int n=0,d1=0,bad=0;for(int x=0;x<512;x++)if(on(x)){n++;int deg=0;for(int y=0;y<9;y++)deg+=on(x^(1<<y));bad+=deg==0?3:max(0,deg-2)*2;d1+=deg==1;}
 int score=bad+abs(d1-2)+3*abs(n-192);if(score<top){top=score;fff=flip;nv=n;errs=bad+abs(d1-2);}}
 ranked.push_back({top,errs,abs(nv-192),j-2,ix++,fff,nv});
 }}
 sort(ranked.begin(),ranked.end());for(auto&row:ranked){for(int x:row)cout<<x<<" ";cout<<"\n";}}

