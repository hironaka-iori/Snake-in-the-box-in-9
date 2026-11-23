#include<algorithm>
#include<array>
#include<cassert>
#include<fstream>
#include<iostream>
#include<numeric>
#include<set>
#include<string>
#include<vector>
using namespace std;using M=__uint128_t;using P=vector<int>;M adj[128],par,mask[7];unsigned char cap[65536];int pc(M m){return __builtin_popcountll(m)+__builtin_popcountll(m>>64);}
int ctz(M x){return (uint64_t)x?__builtin_ctzll(x):64+__builtin_ctzll(x>>64);}
M nbs(M x){M y=0;for(int h=0;h<7;h++){int j=1<<h;y|=(x&mask[h])<<j|(x&~mask[h])>>j;}return y;}
int bound(M x){int n=0;for(int i=0;i<8;i++)n+=cap[(uint16_t)(x>>(i*16))];return n;}
string norm(P p){int ren[8];fill(ren,ren+8,-1);int l=0;string s;for(int i=1;i<p.size();i++){int h=__builtin_ctz(p[i]^p[i-1]);if(ren[h]<0)ren[h]=l++;s+='0'+ren[h];}return s;}
string can(P p){auto f=norm(p);reverse(p.begin(),p.end());return min(f,norm(p));}
int main(int argc,char**argv){for(int v=0;v<128;v++){if(__builtin_parity(v))par|=M(1)<<v;for(int h=0;h<7;h++){adj[v]|=M(1)<<(v^1<<h);if(!(v>>h&1))mask[h]|=M(1)<<v;}}
 for(int z=1;z<65536;z++){bool ok=true;int end=0;for(int v=0;v<16;v++)if(z>>v&1){int d=pc(adj[v]&z);if(d>2)ok=false;if(d<=1)end|=1<<v;}
 int u=end;while(ok){int s=z&(int)nbs(u);if(!(s&~u))break;u|=s;}if(ok&&u==z)cap[z]=__builtin_popcount(z);else for(int s=z;s;s&=s-1)cap[z]=max(cap[z],cap[z&~(s&-s)]);}
 set<string> old;string word;ifstream bas(argv[1]),ex(argv[2]);for(auto*f:{&bas,&ex})while(*f>>word)if(word.size()>=96){P p{0};for(char c:word)p.push_back(p.back()^1<<(c-'0'));old.insert(can(p));}
 int budget=stoi(argv[3]),rid=0;while(cin>>word){P orig{0};for(char c:word)orig.push_back(orig.back()^1<<(c-'0'));int target=96-(int)word.size(); // required number of free Q7 vertices
 int minshape=100,perm[7],chosen[7]{};int lowmask=15;
 for(int lm=1;lm<128;lm++)if(__builtin_popcount(lm)==4){int b=0;for(int h=0;h<7;h++)if(lm>>h&1)perm[h]=b++;for(int h=0;h<7;h++)if(!(lm>>h&1))perm[h]=b++;
 M remaining=~M(0);for(int v:orig)if(v){int y=0;for(int h=0;h<7;h++)if(v>>h&1)y|=1<<perm[h];remaining^=M(1)<<y;}
 int score=bound(remaining);if(score<minshape){minshape=score;copy(perm,perm+7,chosen);}}
 P a;M avail=~M(0);for(int v:orig){int y=0;for(int h=0;h<7;h++)if(v>>h&1)y|=1<<chosen[h];if(v)avail^=M(1)<<y;a.push_back(y);}reverse(a.begin(),a.end());
 P tail{0};int nodes=0,hits=0,nw=0;
 auto dfs=[&](auto&&self,int v,M allowed)->void{if(nodes>=budget)return;nodes++;int depth=tail.size();
  if(depth>=target){P q=a;for(int x:tail)q.push_back(x|128);string k=can(q);hits++;if(old.insert(k).second){nw++;cout<<"NEW "<<k<<" "<<rid<<endl;}if(depth>=target+2)return;}
  M connected=M(1)<<v;for(;;){M more=nbs(connected)&allowed&~connected;if(!more)break;connected|=more;}
  int need=target+(depth>=target)-depth+1;if(pc(connected)<need||bound(connected)<need)return;
  M core=connected;int levels=0;for(;;){M seen=0,two=0;for(int h=0;h<7;h++){int d=1<<h;M t=(core&mask[h])<<d|(core&~mask[h])>>d;two|=seen&t;seen|=t;}
  M reduced=(core&two)|(M(1)<<v);if(reduced==core)break;levels++;core=reduced;if(!core)break;}
  if(bound(core)+levels<need)return;
  M side=(M(1)<<v)&par?par:~par;if(pc(connected&side)<(need+1)/2||pc(connected&~side)<need/2)return;
  M next=adj[v]&connected,remaining=connected&~next&~(M(1)<<v);
  while(next&&nodes<budget){int q=ctz(next);next&=next-1;tail.push_back(q);self(self,q,remaining|M(1)<<q);tail.pop_back();}
 };dfs(dfs,0,avail);cout<<"DONE "<<rid++<<" "<<word.size()<<" "<<minshape<<" "<<nodes<<" "<<hits<<" "<<nw<<" "<<(nodes>=budget?"LIMIT":"EXHAUSTED")<<endl;}
}
