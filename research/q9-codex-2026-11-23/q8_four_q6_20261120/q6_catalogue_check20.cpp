#include<algorithm>
#include<bit>
#include<iostream>
#include<string>
using namespace std;using U=uint64_t;U adj[64];long long N=0,c[64]{};int mx=0,minlen=21;string p;
string norm(string s){int lab[6];fill(lab,lab+6,-1);int k=0;for(char&c:s){int d=c-'0';if(lab[d]<0)lab[d]=k++;c='0'+lab[d];}return s;}
void dfs(int x,U allowed,int next){N++;mx=max(mx,(int)p.size());if((int)p.size()>=minlen&&p<=norm(string(p.rbegin(),p.rend()))){cout<<p<<'\n';c[p.size()]++;}U opts=adj[x]&allowed;U rest=allowed&~(adj[x]|1ull<<x);for(int k=0;k<min(6,next+1);k++){int y=x^1<<k;if(!(opts>>y&1))continue;p+='0'+k;dfs(y,rest,max(next,k+1));p.pop_back();}}
int main(int argc,char**argv){if(argc>1)minlen=stoi(argv[1]);for(int x=0;x<64;x++)for(int i=0;i<6;i++)adj[x]|=1ull<<(x^1<<i);dfs(0,~0ull,0);cerr<<"nodes "<<N<<" max "<<mx;for(int n=minlen;n<=mx;n++)cerr<<" "<<n<<":"<<c[n];cerr<<endl;}
