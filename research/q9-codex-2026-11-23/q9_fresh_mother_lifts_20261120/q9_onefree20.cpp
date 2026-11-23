#include<algorithm>
#include<array>
#include<bit>
#include<cassert>
#include<iostream>
#include<string>
#include<vector>
using namespace std;using M=__uint128_t;using P=vector<int>;M adj[128],mask[7];unsigned char cap[65536];
int pc(M m){return popcount((uint64_t)m)+popcount(uint64_t(m>>64));}int first(M m){return (uint64_t)m?countr_zero((uint64_t)m):64+countr_zero(uint64_t(m>>64));}
M reach1(M x){M y=0;for(int h=0;h<7;h++){int d=1<<h;y|=(x&mask[h])<<d|(x&~mask[h])>>d;}return y;}
int bound(M x){int n=0;for(int i=0;i<8;i++)n+=cap[uint16_t(x>>(16*i))];return n;}
void setup(){for(int v=0;v<128;v++)for(int h=0;h<7;h++){adj[v]|=M(1)<<(v^1<<h);if(!(v>>h&1))mask[h]|=M(1)<<v;}
for(int a=1;a<65536;a++){bool ok=true;int ends=0;for(int x=0;x<16;x++)if(a>>x&1){int k=pc(adj[x]&a);ok&=k<=2;if(k<2)ends|=1<<x;}int comp=ends;while(ok){int o=reach1(comp)&a;if(!(o&~comp))break;comp|=o;}if(ok&&comp==a)cap[a]=popcount(unsigned(a));else for(int s=a;s;s&=s-1)cap[a]=max(cap[a],cap[a&~(s&-s)]);}}
struct Arm{P p;M m;};struct Result{vector<Arm>a;int nodes=0;bool limited=false;};
Result grow(M space,int root,int edges,int budget){Result out;array<int,128> best{},inv{};int top=1000;for(int lm=0;lm<128;lm++)if(popcount(unsigned(lm))==4){
 int b=0,per[7];for(int h=0;h<7;h++)if(lm>>h&1)per[h]=b++;for(int h=0;h<7;h++)if(!(lm>>h&1))per[h]=b++;M img=0;array<int,128> tab{};for(int x=0;x<128;x++){if(x)tab[x]=tab[x&(x-1)]^1<<per[countr_zero(unsigned(x))];if((space>>x)&1)img|=M(1)<<tab[x];}int score=bound(img);if(score<top){top=score;best=tab;}}
 if(top<edges+1)return out;M start=0;for(int x=0;x<128;x++){inv[best[x]]=x;if(space>>x&1)start|=M(1)<<best[x];}
 P path{root};auto dfs=[&](auto&&self,int x,M allowed)->void{if(out.nodes>=budget){out.limited=true;return;}out.nodes++;
 int n=path.size()-1;if(n>=edges){M m=0;for(int j:path)m|=M(1)<<j;out.a.push_back({path,m});}if(n>=50)return;
 M rootbit=M(1)<<x,conn=rootbit;while(1){M more=reach1(conn)&allowed&~conn;if(!more)break;conn|=more;}int need=max(edges,n+1)-n+1;if(pc(conn)<need||bound(conn)<need)return;
 M core=conn;int rounds=0;while(1){M one=0,two=0;for(int h=0;h<7;h++){int k=1<<h;M d=(core&mask[h])<<k|(core&~mask[h])>>k;two|=one&d;one|=d;}M rem=(two&core)|rootbit;if(rem==core)break;core=rem;rounds++;}if(bound(core)+rounds<need)return;
 M next=adj[x]&conn,remain=conn&~(next|rootbit);while(next){int v=first(next);next&=next-1;path.push_back(inv[v]);self(self,v,remain|M(1)<<v);path.pop_back();if(out.limited)break;}};dfs(dfs,best[root],start);return out;}
bool valid(const P&p){for(int j=0;j<p.size();j++){if(p[j]<0||p[j]>=512)return false;for(int i=0;i<j;i++){int d=popcount(unsigned(p[i]^p[j]));if(!d||(d==1)!=(j==i+1))return false;}}return true;}
struct Z{array<M,2> v{};};
Z both(Z a,Z b){return {{a.v[0]&b.v[0],a.v[1]&b.v[1]}};}Z rem(Z a,Z b){return {{a.v[0]&~b.v[0],a.v[1]&~b.v[1]}};}Z add(Z a,Z b){return {{a.v[0]|b.v[0],a.v[1]|b.v[1]}};}bool same(Z a,Z b){return a.v==b.v;}Z singleton(int i){Z r;r.v[i>>7]=M(1)<<(i&127);return r;}Z n8(Z a){return {{reach1(a.v[0])|a.v[1],reach1(a.v[1])|a.v[0]}};}int count8(Z a){return pc(a.v[0])+pc(a.v[1]);}int bound8(Z a){return bound(a.v[0])+bound(a.v[1]);}
struct Free{int nodes=0;bool limited=false;P path;};
Free open8(Z space,int root,int goal,int capnodes){Free out;P walk{root};auto dfs=[&](auto&&self,int x,Z free)->bool{if(out.nodes++>=capnodes){out.limited=true;return false;}int n=walk.size()-1;if(n>=goal){out.path=walk;return true;}Z X=singleton(x),cc=X;while(1){auto z=add(cc,both(n8(cc),free));if(same(z,cc))break;cc=z;}int need=goal-n+1;if(count8(cc)<need||bound8(cc)<need)return false;
 Z core=cc;int passes=0;while(1){Z after{};for(int i=0;i<2;i++){M one=core.v[1-i],two=0;for(int k=0;k<7;k++){int z=1<<k;M dir=(core.v[i]&mask[k])<<z|(core.v[i]&~mask[k])>>z;two|=one&dir;one|=dir;}after.v[i]=two&core.v[i];}after=add(after,X);if(same(after,core))break;core=after;passes++;}if(bound8(core)+passes<need)return false;
 Z cand=both(n8(X),cc),rest=rem(rem(cc,X),cand);for(int h=0;h<2;h++){M c=cand.v[h];while(c){int y=first(c)+128*h;c&=c-1;walk.push_back(y);if(self(self,y,add(rest,singleton(y))))return true;walk.pop_back();if(out.limited)return false;}}return false;};dfs(dfs,root,space);return out;}
int main(int argc,char**argv){setup();int target=stoi(argv[1]),amin=stoi(argv[2]),acap=stoi(argv[3]),bcap=stoi(argv[4]),maxopts=stoi(argv[5]);string w;int job=0;
 while(cin>>w){P orig{0};for(char c:w)orig.push_back(orig.back()^1<<(c-'0'));assert(valid(orig));long long nt=0,nf=0;size_t nA=0,tried=0,condOpen=0,armlimits=0;bool found=false;
 for(int rev=0;rev<2&&!found;rev++){P mid=orig;if(rev)reverse(mid.begin(),mid.end());int s=mid.front(),t=mid.back(),remain=target-(int)w.size()-2;Z avail{{~M(0),~M(0)}};for(int x:mid)avail=rem(avail,singleton(x));avail=add(avail,singleton(t));
 for(int ax=0;ax<8&&!found;ax++){int ua=1<<ax;auto pr=[&](int v){return (v&(ua-1))|((v>>(ax+1))<<ax);};auto up=[&](int v){return (s&ua)|(v&(ua-1))|((v>>ax)<<(ax+1));};M anchor=~M(0);
 for(int x:mid)if((x&ua)==(s&ua))anchor&=~(M(1)<<pr(x));anchor|=M(1)<<pr(s);
 for(int y=0;y<128;y++)if(popcount(unsigned(up(y)^t))<=1)anchor&=~(M(1)<<y);
 if(!(anchor>>pr(s)&1))continue;auto A=grow(anchor,pr(s),amin,acap);nt+=A.nodes;armlimits+=A.limited;nA+=A.a.size();sort(A.a.begin(),A.a.end(),[](auto&a,auto&b){return a.p.size()>b.p.size();});
 int seen=0;for(auto&a:A.a){if(seen++>=maxopts)break;tried++;Z block{};for(int x:a.p)block=add(block,singleton(up(x)));Z free=rem(avail,add(block,n8(block)));auto rr=open8(free,t,remain-((int)a.p.size()-1),bcap);nf+=rr.nodes;condOpen+=rr.limited;if(rr.path.empty())continue;
 P output;for(auto it=a.p.rbegin();it!=a.p.rend();it++)output.push_back(up(*it)+256);output.insert(output.end(),mid.begin(),mid.end());for(int x:rr.path)output.push_back(x+256);assert(valid(output));cout<<"FOUND "<<job<<" "<<ax<<" "<<output.size()-1<<" "<<w;for(int x:output)cout<<" "<<x;cout<<endl;found=true;break;}}}
 cout<<"DONE "<<job++<<" "<<w<<" "<<nA<<" "<<tried<<" "<<armlimits<<" "<<condOpen<<" "<<nt<<" "<<nf<<endl;}}
