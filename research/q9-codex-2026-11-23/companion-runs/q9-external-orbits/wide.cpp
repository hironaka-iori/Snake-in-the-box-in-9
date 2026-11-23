#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using U=uint64_t;using Perm=array<int,512>;using T=chrono::steady_clock;
int wt(int x){return popcount(unsigned(x));}int low(U b){return countr_zero(b);}mt19937 gen;int rnd(int n){return gen()%n;}
Perm swapAt(int a,int b,int center){Perm f;for(int x=0;x<512;x++){int y=x^center;f[x]=x^((((y>>a)^(y>>b))&1)? (1<<a|1<<b):0);}return f;}
Perm shift(int t){Perm f;for(int x=0;x<512;x++)f[x]=x^t;return f;}
struct Group{vector<P> orb;array<int,512> id;bool create(vector<Perm> const&g){id.fill(-1);orb.clear();for(int x=0;x<512;x++)if(id[x]<0){int k=orb.size();P q{x};id[x]=k;for(int i=0;i<q.size();i++)for(auto&f:g){int y=f[q[i]];if(id[y]<0){id[y]=k;q.push_back(y);if(q.size()>32)return false;}}orb.push_back(q);}return true;}};
struct Edge{int v;vector<U> ok;};struct Solver{P p,solution;int n,limit;long long nodes=0;vector<P> dom;vector<U> masks;vector<vector<Edge>> adj;vector<pair<int,U>> changes;
 Solver(P const&path,Group const&g,int cap):p(path),n(path.size()),limit(cap),dom(n),masks(n),adj(n){for(int i=0;i<n;i++){dom[i]=g.orb[g.id[p[i]]];masks[i]=(1ull<<dom[i].size())-1;}
 for(int i=0;i<n;i++)for(int j=0;j<i;j++){bool near=i==j+1;if(!near){bool maybe=false;for(int v:dom[j])if(wt(p[i]^v)<=1){maybe=true;break;}if(!maybe)continue;}
 vector<U> left(dom[i].size()),right(dom[j].size());bool blocked=false;
 for(int a=0;a<dom[i].size();a++)for(int b=0;b<dom[j].size();b++){int d=wt(dom[i][a]^dom[j][b]);if(near?d==1:d>=2){left[a]|=1ull<<b;right[b]|=1ull<<a;}else blocked=true;}
 if(blocked){adj[i].push_back({j,move(left)});adj[j].push_back({i,move(right)});}}
 }
 void assign(int i,U m){changes.emplace_back(i,masks[i]);masks[i]=m;}
 bool propagate(P queue){for(int h=0;h<queue.size();h++){int i=queue[h];for(auto&e:adj[i]){U avail=0;for(U a=masks[i];a;a&=a-1)avail|=e.ok[low(a)];U b=avail&masks[e.v];if(!b)return false;if(b!=masks[e.v]){assign(e.v,b);queue.push_back(e.v);}}}return true;}
 int search(){if(++nodes>limit)return -1;int best=-1,which=-1,weight=100000;for(int i=0;i<n;i++){int sz=popcount(masks[i]);if(sz<=1)continue;int v=sz*2000-int(adj[i].size());if(v<weight){which=i;weight=v;}}
 if(which<0){solution.clear();for(int i=0;i<n;i++)solution.push_back(dom[i][low(masks[i])]);return 1;}
 int i=which;U opts=masks[i];int old=0;while(dom[i][old]!=p[i])old++;U preferred=1ull<<old;
 while(opts){U a=(preferred&opts)?preferred:opts&-opts;opts^=a;auto trail=changes.size();assign(i,a);int result=0;if(propagate({i}))result=search();if(result)return result;while(changes.size()>trail){auto [j,b]=changes.back();changes.pop_back();masks[j]=b;}}return 0;}
 int solve(Group const&g){int pivot=0;for(int i=1;i<n;i++)if(dom[i].size()>dom[pivot].size())pivot=i;
 int a=find(dom[pivot].begin(),dom[pivot].end(),p[pivot])-dom[pivot].begin();assign(pivot,1ull<<a);P q(n);iota(q.begin(),q.end(),0);if(!propagate(q))return 0;return search();}
};
bool valid(P const&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){int d=wt(p[i]^p[j]);if(i==j+1?d!=1:d<2)return false;}return true;}
int main(int argc,char**argv){if(argc!=6)return 1;int mode=atoi(argv[1]),reps=atoi(argv[2]),cap=atoi(argv[3]),sec=atoi(argv[4]);gen.seed(strtoul(argv[5],nullptr,10));vector<P>bank;string line;while(getline(cin,line)){istringstream s(line);P p;int z;while(s>>z)p.push_back(z);bank.push_back(p);}
 long long tested=0,unsat=0,unknown=0,found=0,nodes=0;array<int,7> fam{};auto start=T::now();vector<set<vector<int>>>seen(bank.size());
 for(int rep=0;rep<reps;rep++)for(int i=0;i<bank.size();i++){auto&p=bank[i];int u=0,v=0;for(int a=0;a<p.size()&&!v;a++)for(int b=a+2;b<p.size();b++)if(wt(p[a]^p[b])<=1){u=a;v=b;break;}
 int typ=mode?rep%6:6;int c=mode?(rep%4?p[rnd(2)?u:v]:rnd(512)):37;array<int,9>d;iota(d.begin(),d.end(),0);shuffle(d.begin(),d.end(),gen);
 if(mode&&rep%2){int k=u?p[u]^p[u-1]:p[u]^p[u+1];int j=countr_zero(unsigned(k));if(j<9)iter_swap(d.begin(),find(d.begin(),d.end(),j));}
 vector<Perm>gs;auto sw=[&](int j,int k){gs.push_back(swapAt(d[j],d[k],c));};auto tr=[&](int j,int k){gs.push_back(shift(1<<d[j]|1<<d[k]));};
 if(typ==0){for(int k=1;k<5;k++)tr(0,k);}
 if(typ==1){for(int k=1;k<6;k++)tr(0,k);}
 if(typ==2){for(int k=0;k<5;k++)sw(k,k+1);}
 if(typ==3){for(int k=0;k<4;k++)sw(k,k+1);tr(5,6);tr(5,7);}
 if(typ==4){for(int k=1;k<4;k++)tr(0,k);sw(4,5);sw(5,6);}
 if(typ==5){for(int k=1;k<5;k++)tr(0,k);sw(5,6);}
 if(typ==6){gs={swapAt(0,2,37),swapAt(2,5,37)};}
 Group g;if(!g.create(gs))continue;vector<int> signature(g.id.begin(),g.id.end());if(!seen[i].insert(signature).second)continue;
 Solver sol(p,g,cap);int res=sol.solve(g);nodes+=sol.nodes;++tested;fam[typ]++;if(res>0){if(!valid(sol.solution))abort();++found;cout<<i<<" "<<rep;for(int x:sol.solution)cout<<" "<<x;cout<<endl;if(mode)goto done;}else if(res<0)unknown++;else unsat++;
 if(chrono::duration<double>(T::now()-start).count()>=sec)goto done;}
 done:cerr<<"tested "<<tested<<" unsat "<<unsat<<" unknown "<<unknown<<" found "<<found<<" nodes "<<nodes<<" families";for(int v:fam)cerr<<" "<<v;cerr<<endl;}

