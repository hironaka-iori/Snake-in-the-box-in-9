#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using Mask=array<unsigned long long,4>;
void setbit(Mask&m,int v){m[v>>6]|=1ULL<<(v&63);}
void clearbit(Mask&m,int v){m[v>>6]&=~(1ULL<<(v&63));}
void neighborhood(Mask&m,int x){setbit(m,x);for(int d=0;d<8;d++)setbit(m,x^(1<<d));}
bool overlap(const Mask&a,const Mask&b){return ((a[0]&b[0])|(a[1]&b[1])|(a[2]&b[2])|(a[3]&b[3]))!=0;}
using Duo=array<vector<int>,2>;struct Tail{Mask occ{},near{},tipnear{};vector<int>v;};
struct Joined{int a,b;};
unsigned rng=4288151;unsigned rd(){rng^=rng<<13;rng^=rng>>17;return rng^=rng<<5;}
array<int,256>block;array<bool,256>tipOK;vector<Tail>res;vector<int>path;bool cut;int depth,nodeLimit,pathLimit,nodes;long long allNodes=0,probed=0,assemblies=0;
void ban(int v,int e){block[v]+=e;for(int d=0;d<8;d++)block[v^(1<<d)]+=e;}
void dfs(int v){if(cut)return;if(++nodes>nodeLimit){cut=true;return;}if(path.size()==depth){if(tipOK[v]){Tail t;t.v=path;for(int x:path){setbit(t.occ,x);neighborhood(t.near,x);}neighborhood(t.tipnear,v);res.push_back(move(t));if(res.size()>=pathLimit)cut=true;}return;}
 int next[8],n=0;for(int i=0;i<8;i++){int x=v^(1<<i);if(!block[x])next[n++]=x;}ban(v,1);
 for(int j=n-1;j>=0&&!cut;j--){int k=rd()%(j+1),x=next[k];swap(next[k],next[j]);path.push_back(x);dfs(x);path.pop_back();}ban(v,-1);}
vector<Tail> grow(const Duo&cores,int side,int back,int length){block.fill(0);tipOK.fill(true);
 auto&c=cores[side];auto&other=cores[1-side];int anchor=back?c.back():c.front();
 for(auto v:c)if(v!=anchor)ban(v,1);for(auto v:other){block[v]++;if(back&&side){tipOK[v]=false;for(int d=0;d<8;d++)tipOK[v^(1<<d)]=false;}}
 cut=false;nodes=0;depth=length;res.clear();path.clear();dfs(anchor);allNodes+=nodes;return move(res);}
bool verify(const Duo&p){vector<int>z(p[0].rbegin(),p[0].rend());for(int v:p[1])z.push_back(256+v);z.push_back(p[1].back());for(int i=0;i<z.size();i++)for(int j=0;j<i;j++)if(z[j]==z[i]||((popcount(unsigned(z[j]^z[i]))==1)!=(j+1==i)))return false;return true;}
int main(int argc,char**argv){assert(argc==6);ifstream f(argv[1]);int n,m;vector<Duo>pool;while(f>>n>>m){Duo p;p[0].resize(n);p[1].resize(m);for(auto&a:p)for(auto&v:a)f>>v;pool.push_back(p);}int calls=stoi(argv[2]);nodeLimit=stoi(argv[3]);pathLimit=stoi(argv[4]);int control=stoi(argv[5]),best=0;
 long long completed=0,geom=0,live=0,found=0;
 for(int it=0;it<calls;it++){int id=control?it%pool.size():(it%3?rd()%min(size_t(12),pool.size()):rd()%pool.size());auto &base=pool[id];Duo cores;int k[2],l[2],goal[2]={96,96};if(control){assert(verify(base));goal[0]=base[0].size();goal[1]=base[1].size();}else if(it%5==4)goal[rd()%2]--;
 bool ok=true;for(int s=0;s<2;s++){int front=2+rd()%(control?4:18),back=2+rd()%(control?4:24);int drift=control?0:(int(rd()%5)-2);k[s]=front+drift;l[s]=back+goal[s]-int(base[s].size())-drift;if(min(k[s],l[s])<1){ok=false;break;}cores[s].assign(base[s].begin()+front,base[s].end()-back);}
 if(!ok)continue;Mask c0{};for(int x:cores[0])setbit(c0,x);for(int x:cores[1]){Mask m{};setbit(m,x);if(overlap(c0,m))ok=false;}if(!ok)continue;geom++;bool full=true;
 array<vector<Tail>,4>w;for(int j=0;j<4;j++){w[j]=grow(cores,j%2,j/2,j<2?k[j%2]:l[j%2]);full&=!cut;if(w[j].empty()){ok=false;break;}}
 if(full)completed++;if(!ok)continue;
 vector<Joined>front,back;
 for(int i=0;i<w[0].size();i++)for(int j=0;j<w[1].size();j++){auto &a=w[0][i],&b=w[1][j];if(a.v.back()!=b.v.back())continue;auto m=a.occ;clearbit(m,a.v.back());if(!overlap(m,b.occ))front.push_back({i,j});}
 if(front.empty())continue;
 for(int i=0;i<w[2].size();i++)for(int j=0;j<w[3].size();j++){auto &a=w[2][i],&b=w[3][j];if(!overlap(a.occ,b.occ)&&!overlap(a.occ,b.tipnear))back.push_back({i,j});}
 if(back.empty())continue;live++;long long checked=0;
 for(auto F:front)for(auto B:back){if(++checked>200000){if(full)completed--;goto next;}probed++;auto&a=w[0][F.a],&b=w[1][F.b],&x=w[2][B.a],&y=w[3][B.b];
 if(overlap(a.near,x.occ)||overlap(b.near,y.occ)||overlap(a.occ,y.occ)||overlap(b.occ,x.occ)||overlap(a.occ,y.tipnear))continue;
 assemblies++;{Duo p=cores;for(int s=0;s<2;s++){auto&fr=s?b:a;auto&ba=s?y:x;p[s].insert(p[s].begin(),fr.v.rbegin(),fr.v.rend());p[s].insert(p[s].end(),ba.v.begin(),ba.v.end());assert(p[s].size()==goal[s]);}assert(verify(p));found++;if(goal[0]+goal[1]>best){best=goal[0]+goal[1];cout<<"BEST "<<best<<" "<<it<<" "<<id<<" "<<goal[0]<<" "<<goal[1];for(auto&arm:p)for(auto v:arm)cout<<" "<<v;cout<<endl;if(!control&&best>=192)return 0;}}goto next;
 }next:;
 }cout<<"DONE "<<calls<<" geometries "<<geom<<" uncapped_in_visited_work "<<completed<<" both_joins_nonempty "<<live<<" nodes "<<allNodes<<" pairchecks "<<probed<<" hits "<<found<<" best "<<best<<endl;}
