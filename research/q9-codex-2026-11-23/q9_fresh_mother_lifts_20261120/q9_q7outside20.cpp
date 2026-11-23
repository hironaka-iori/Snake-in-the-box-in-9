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
int main(int argc,char**argv){setup();int goal=stoi(argv[1]),budget=stoi(argv[2]),i=0;string w;while(cin>>w){P middle{0};for(char c:w)middle.push_back(middle.back()^1<<(c-'0'));assert(valid(middle));
 int remain=goal-w.size()-2;int claimed=0,excluded=0,total=0,open=0;long long ns=0,pa=0,combs=0;
 for(int axis=0;axis<8;axis++){int ia=1<<axis;if(!(middle.back()&ia))continue;total++;
 auto pr=[&](int v){return (v&(ia-1))|((v>>(axis+1))<<axis);};auto lift=[&](int v,int side){return (v&(ia-1))|((v>>axis)<<(axis+1))|side*ia|256;};
 int r[]={pr(middle.front()),pr(middle.back())};if(r[0]==r[1]){excluded++;continue;}M free[2]={~M(0),~M(0)};
 for(int x:middle)free[(x>>axis)&1]&=~(M(1)<<pr(x));for(int h=0;h<2;h++){free[h]|=M(1)<<r[h];free[h]&=~(M(1)<<r[1-h]);}
 // Start with the more obstructed half, retain every long enough rooted path.
 int h=pc(free[0])<pc(free[1])?0:1;
 auto A=grow(free[h],r[h],max(1,remain-50),budget);ns+=A.nodes;pa+=A.a.size();if(A.a.empty()&&!A.limited){excluded++;continue;}
 int mx=0;for(auto&a:A.a)mx=max(mx,(int)a.p.size()-1);auto B=grow(free[1-h],r[1-h],max(1,remain-(A.limited?50:mx)),budget);ns+=B.nodes;pa+=B.a.size();if(B.a.empty()&&!B.limited){excluded++;continue;}
 for(auto&a:A.a)for(auto&b:B.a)if((int)(a.p.size()+b.p.size())>=remain+2){combs++;if(a.m&b.m)continue;auto& l=h==0?a:b;auto&rr=h==0?b:a;P full;for(auto it=l.p.rbegin();it!=l.p.rend();++it)full.push_back(lift(*it,0));full.insert(full.end(),middle.begin(),middle.end());for(int v:rr.p)full.push_back(lift(v,1));assert(valid(full));cout<<"FOUND "<<i<<" "<<axis<<" "<<full.size()-1<<" "<<w;for(auto v:full)cout<<" "<<v;cout<<endl;claimed++;goto endcase;}
 if(A.limited||B.limited)open++;else excluded++;
 endcase:;}
 cout<<"DONE "<<i++<<" "<<w<<" "<<total<<" "<<excluded<<" "<<open<<" "<<claimed<<" "<<ns<<" "<<pa<<" "<<combs<<endl;}}
