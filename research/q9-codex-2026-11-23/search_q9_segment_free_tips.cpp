#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Bits=array<unsigned long long,4>;
int target,trim,cap,best=-1;
long long intervals=0,legal=0,bodies=0,nodes=0,capped=0;
unordered_set<string> seen;
struct Growth {
 deque<int> path; array<int,512> covered{},used{}; int visits=0; bool limited=false;
 void toggle(int v,int sign){used[v]+=sign;for(int d=0;d<9;d++)covered[v^(1<<d)]+=sign;}
 void dfs(bool left){
 if(limited)return;
 if(++visits>cap){limited=true;return;}
 best=max(best,int(path.size())-1);
 if(int(path.size())-1>=target){
 for(int i=0;i<int(path.size());i++)for(int j=0;j<i;j++){
 int dx=__builtin_popcount(path[i]^path[j]); if(dx==0 || ((dx==1)!=(i==j+1)))abort();}
 cout<<"FOUND";for(int v:path)cout<<" "<<v;cout<<endl;exit(0);}
 for(int d=0;d<9;d++){int v=(left?path.front():path.back())^(1<<d);
 if(used[v]||covered[v]!=1)continue;
 toggle(v,1);if(left)path.push_front(v);else path.push_back(v);
 dfs(left);if(left)path.pop_front();else path.pop_back();toggle(v,-1);if(limited)return;}
 if(!left)dfs(true);
 }
};
bool any(const Bits &s,int a,int b){if(a>b)return false;for(int w=a/64;w<=b/64;w++){
 auto m=~0ULL;if(w==a/64)m&=(~0ULL<<(a%64));if(w==b/64)m&=(~0ULL>>(63-b%64));if(m&s[w])return true;}return false;}
int main(int argc,char**argv){
 if(argc!=4 && argc!=5)return 2;target=atoi(argv[1]);trim=atoi(argv[2]);cap=atoi(argv[3]);
 string line;int seeds=0;
 while(getline(cin,line)){istringstream in(line);vector<int>p;int x;while(in>>x)p.push_back(x);int n=p.size();if(n<100||n>240)abort();
 int a=-1,b=-1;for(int k=0;k<n;k++)for(int h=0;h<k;h++){int dist=__builtin_popcount(p[k]^p[h]);if(!dist||((h+1==k)&&dist!=1))abort();if(h+1<k&&dist==1){if(a!=-1)abort();a=h;b=k;}}if(a<0)abort();seeds++;
 array<Bits,512> near{};for(int k=0;k<n;k++)for(int d=-1;d<9;d++){int v=p[k]^(d<0?0:1<<d);near[v][k/64]|=1ULL<<(k%64);}
 for(int u=0;u<9;u++)for(int v=0;v<u;v++)for(int axes=0;axes<(argc==5?81:1);axes++){
 int c=axes/9,d=axes%9;bool two=argc==5;
 if(two && (c<=d || c>=u || c==v || d==v))continue;
 for(int parity=0;parity<(two?4:2);parity++){
 vector<int> t(n);vector<Bits> clash(n);
 for(int k=0;k<n;k++){int flip=(((p[k]>>u)^(p[k]>>v))&1)^(parity&1);t[k]=p[k]^(flip?((1<<u)|(1<<v)):0);if(two && (((((p[k]>>c)^(p[k]>>d))&1)^(parity>>1))!=0))t[k]^=(1<<c)|(1<<d);clash[k]=near[t[k]];for(int h=max(0,k-1);h<=min(k+1,n-1);h++)clash[k][h/64]&=~(1ULL<<(h%64));}
 for(int i=1;i<n-2;i++){if(t[i]!=p[i]||i>b)continue;Bits bad{};int changed=0;
 for(int j=i;j<n-1;j++){changed+=t[j]!=p[j];for(int w=0;w<4;w++)bad[w]|=clash[j][w];
 if(t[j]!=p[j]||changed<3||((a>=i&&a<=j)==(b>=i&&b<=j)))continue;
 intervals++;if(any(bad,trim,i-1)||any(bad,j+1,n-trim-1))continue;
 int l=0,r=0;for(int h=min(i-1,trim-1);h>=0;h--)if(any(bad,h,h)){l=h+1;break;}
 for(int h=max(j+1,n-trim);h<n;h++)if(any(bad,h,h)){r=n-h;break;}
 if(l+r>trim)continue;legal++;
 for(int L=l;L<=min(i,l+4);L++)for(int R=r;R<=min(n-1-j,r+4)&&R+L<=trim;R++){
 string key;for(int k=L+1;k<n-R;k++){int e=k>=i&&k<=j?t[k]:p[k];int f=k-1>=i&&k-1<=j?t[k-1]:p[k-1];key.push_back(char(__builtin_ctz(e^f)));}
 if(!seen.insert(key).second)continue;
 Growth g;for(int k=L;k<n-R;k++){int e=k>=i&&k<=j?t[k]:p[k];g.path.push_back(e);g.toggle(e,1);}g.dfs(false);bodies++;nodes+=g.visits;capped+=g.limited;}
 }}}}
 }cout<<"seeds "<<seeds<<" intervals "<<intervals<<" repairable "<<legal<<" distinct_bodies "<<bodies<<" growth_nodes "<<nodes<<" capped "<<capped<<" best_edges "<<best<<endl;
 return 0;
}
