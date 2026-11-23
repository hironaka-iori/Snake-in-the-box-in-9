#include <algorithm>
#include <array>
#include <bit>
#include <set>
#include <chrono>
#include <iostream>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using T=array<P,3>;using M=array<uint64_t,4>;
int nb[256][8],deg[256],on[256],target,bound,sec,total,goal,maxlen,best=0;long long trials,dfsCount,raw=0;set<M> seen;P a,b,c,graft;chrono::steady_clock::time_point start;
void mark(int x,int s){on[x]=s>0;for(int y:nb[x])deg[y]+=s;}
void save(){if(total+graft.size()<target)return;M m{};for(int x=0;x<256;x++)if(on[x])m[x/64]|=1ull<<(x%64);if(!seen.insert(m).second)return;int n=total+graft.size();best=max(best,n);if(++raw>90000&&n<100)return;int zero=a[0];cout<<a.size()+b.size()+graft.size();for(auto*q:{&a,&graft,&b})for(int x:*q)cout<<" "<<(x^zero);cout<<" "<<c.size();for(int x:c)cout<<" "<<(x^zero);cout<<endl;}
void dfs(int cur){++dfsCount;if(graft.size()>=maxlen)return;
 for(int y:nb[cur]){if(on[y])continue;int d=deg[y];if(d==1){mark(y,1);graft.push_back(y);dfs(y);graft.pop_back();mark(y,-1);}
 else if(d==2 && popcount(unsigned(y^goal))==1){mark(y,1);graft.push_back(y);save();graft.pop_back();mark(y,-1);}}
}
int main(int argc,char**argv){if(argc!=4)return 1;target=atoi(argv[1]);bound=atoi(argv[2]);sec=atoi(argv[3]);start=chrono::steady_clock::now();for(int x=0;x<256;x++)for(int d=0;d<8;d++)nb[x][d]=x^(1<<d);string s;vector<T> donors;
 while(getline(cin,s)){T tri;istringstream in(s);int n,x;for(auto&w:tri){if(!(in>>n))return 1;while(n--){in>>x;w.push_back(x);}}donors.push_back(tri);}
 for(int k=0;k<=bound;k++)for(const T&o:donors)for(int fix=0;fix<3;fix++)for(int ori=0;ori<4;ori++){auto l=o[(fix+1)%3],r=o[(fix+2)%3];if(ori&1)reverse(l.begin(),l.end());if(ori&2)reverse(r.begin(),r.end());c=o[fix];
 for(int dl=0;dl<=k;dl++){int dr=k-dl;if(dl>=l.size()||dr>=r.size())continue;a={l.begin(),l.end()-dl};b={r.begin()+dr,r.end()};goal=b[0];total=a.size()+b.size()+c.size();
 for(auto*q:{&a,&b,&c})for(int x:*q)mark(x,1);maxlen=min(26,max(7,k+4));++trials;dfs(a.back());for(auto*q:{&a,&b,&c})for(int x:*q)mark(x,-1);
 if((trials&16383)==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>=sec)goto done;
 }}
 done:cerr<<"donors "<<donors.size()<<" bridge_cores "<<trials<<" dfs "<<dfsCount<<" saved "<<raw<<" max "<<best<<endl;
}

