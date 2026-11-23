#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using Clock=chrono::steady_clock;
mt19937 rng;int draw(int n){return rng()%n;}int wt(int v){return popcount(unsigned(v));}
bool correct(P const&p){for(int a=0;a<p.size();a++)for(int b=0;b<a;b++){int wt0=wt(p[a]^p[b]);if(a==b+1?wt0!=1:wt0<2)return false;}return true;}
struct Solve{array<P,4> pieces;array<array<int,9>,4> map{},order{};int occ[512]{},deg[512]{},available[4]{},cap=0;P path,sol;long long nodes=0;bool cutoff=false,ctrl=false;
 void mark(int x,int s){occ[x]=s>0;for(int d=0;d<9;d++)deg[x^(1<<d)]+=s;}
 bool tryNew(int j,int ix,int y){if(occ[y]||deg[y]!=1)return false;path.push_back(y);mark(y,1);bool ok=run(j,ix+1);mark(y,-1);path.pop_back();return ok;}
 bool run(int j,int ix){if(++nodes>cap){cutoff=true;return false;}if(j==4){sol=path;return true;}if(ix==pieces[j].size())return run(j+1,0);
 int last=path.back();auto&ord=order[j];
 if(!ix){int pref=last^pieces[j][0];if(wt(pref)==1&&tryNew(j,ix,pieces[j][0]))return true;for(int d:ord){int y=last^(1<<d);if(y==pieces[j][0])continue;if(tryNew(j,ix,y))return true;if(cutoff)break;}return false;}
 int b=countr_zero(unsigned(pieces[j][ix]^pieces[j][ix-1])),k=map[j][b];if(k>=0)return tryNew(j,ix,last^(1<<k));
 for(int u=0;u<10;u++){int d=u==0?b:ord[u-1];if((u&&d==b)||!(available[j]>>d&1))continue;
 map[j][b]=d;available[j]^=1<<d;bool ok=tryNew(j,ix,last^(1<<d));map[j][b]=-1;available[j]^=1<<d;if(ok)return true;if(cutoff)break;}return false;}
 bool solve(){for(int j=0;j<4;j++){iota(order[j].begin(),order[j].end(),0);if(!ctrl)shuffle(order[j].begin(),order[j].end(),rng);map[j].fill(-1);available[j]=511;}
 for(int x:pieces[0]){path.push_back(x);mark(x,1);}return run(1,0);}
};
int main(int argc,char**argv){if(argc!=6)return 1;int ctrl=atoi(argv[1]),reps=atoi(argv[2]),cap=atoi(argv[3]),sec=atoi(argv[4]);rng.seed(strtoul(argv[5],nullptr,10));string line;vector<P>bank;while(getline(cin,line)){istringstream in(line);P p;int x;while(in>>x)p.push_back(x);bank.push_back(p);}
 long long trials=0,nodes=0,cut=0,found=0;auto start=Clock::now();for(int it=0;it<reps;it++)for(int j=0;j<bank.size();j++){P p=bank[j];int a=0,b=0;
 if(ctrl){a=70;b=a+17;}else for(int k=0;k<p.size()&&!b;k++)for(int l=k+2;l<p.size();l++)if(wt(p[k]^p[l])==1){a=k;b=l;break;}
 if(b-a!=17)return 3;if(a<p.size()-1-b){reverse(p.begin(),p.end());int prev=a;a=p.size()-1-b;b=p.size()-1-prev;}
 Solve s;s.cap=cap;s.ctrl=ctrl;s.pieces[0]={p.begin(),p.begin()+a};s.pieces[3]={p.begin()+b+1,p.end()};P cyc(p.begin()+a,p.begin()+b+1);
 int dir=ctrl?1:(draw(2)?1:-1),st=ctrl?0:draw(18),k=ctrl?8:2+draw(15);for(int h=0;h<18;h++)s.pieces[h<k?1:2].push_back(cyc[(st+dir*h+36)%18]);
 if(!ctrl&&draw(2))reverse(s.pieces[2].begin(),s.pieces[2].end());
 if(!ctrl&&draw(5)==0)reverse(s.pieces[3].begin(),s.pieces[3].end());trials++;
 if(s.solve()){if(!correct(s.sol))abort();found++;cout<<j<<" "<<it;for(int x:s.sol)cout<<" "<<x;cout<<endl;if(!ctrl)goto done;}nodes+=s.nodes;cut+=s.cutoff;
 if(chrono::duration<double>(Clock::now()-start).count()>=sec)goto done;}
 done:cerr<<"templates "<<trials<<" explored_nodes "<<nodes<<" capped "<<cut<<" found "<<found<<endl;}

