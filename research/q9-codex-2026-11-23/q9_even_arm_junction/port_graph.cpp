#define main brute_driver
#include "brute.cpp"
#undef main
struct Edge{int mask,child;};struct Node{vector<Edge>next;int leaf=-1,maxRank=-1;};
vector<Node>trie(1);vector<P>arms;vector<int>order,rankOf;
void put(const P&ms,int id){int n=0;for(int m:ms){int c=-1;for(auto e:trie[n].next)if(e.mask==m)c=e.child;if(c<0){c=trie.size();trie[n].next.push_back({m,c});trie.emplace_back();}n=c;trie[n].maxRank=max(trie[n].maxRank,rankOf[id]);}trie[n].leaf=id;}
U tests=0,nodes=0,terms=0,leftWorks=0,capRows=0;bool won=false;
struct Join{
 P a,b{0};array<int,512>al,bl,edge,capB{};array<unsigned short,512>load{};array<int,2500>mult{};array<int,50>deg{};array<bool,512>allowed{};array<int,9>img;unsigned used=0;int zeroA=0,oneA=0,zeroB=0,oneB=0;U local=0,limit;int id,cutRank;bool control;
 Join(const P&ms,int i,int cut,U cap,bool ctl):a(anchors(ms)),limit(cap),id(i),cutRank(cut),control(ctl){
  al.fill(-1);bl.fill(-1);bl[0]=0;edge.fill(-1);img.fill(-1);
  for(int j=0;j<a.size();j++){int v=a[j];al[v]=j;for(int k=1;k<512;k*=2)load[v^k]|=k;}
  for(int o=0;o<512;o++){unsigned m=load[o];allowed[o]=!m||(has_single_bit(m)&&int(m)==o);if(popcount(m)!=2)continue;int v=o^(m&-m);m&=m-1;int w=o^m;int x=al[v],y=al[w];if(x>y)swap(x,y);edge[o]=50*x+y;if(!mult[edge[o]]++){deg[x]++;deg[y]++;}}
  for(int j=0;j<a.size();j++){zeroA+=!deg[j];oneA+=j>0&&deg[j]==1;}
 }
 void bumpA(int i,int delta){int d=deg[i];zeroA+=(d+delta==0)-(d==0);oneA+=(i>0)*((d+delta==1)-(d==1));deg[i]+=delta;}
 void bumpB(int v,int delta){if(!v)return;int d=capB[v];zeroB+=(d+delta==0)-(d==0);oneB+=(d+delta==1)-(d==1);capB[v]+=delta;}
 void toggle(int y,bool add){if(!add){zeroB-=capB[y]==0;oneB-=capB[y]==1;b.pop_back();bl[y]=-1;}
  int initial=0;
  for(int d=1;d<512;d*=2){int o=y^d;if(!add)load[o]^=d;unsigned m=load[o];if(allowed[o]&&popcount(m)<=1)initial++;
   if(popcount(m)==2){if(edge[o]>=0){int e=edge[o],delta=add?-1:1;bool real=add?mult[e]==1:mult[e]==0;mult[e]+=delta;if(real){bumpA(e/50,delta);bumpA(e%50,delta);}}
    else if(allowed[o]){int x=o^(m&-m);int z=o^(m&(m-1));if(x)bumpB(x,add?-1:1);if(z)bumpB(z,add?-1:1);}}
   if(add)load[o]^=d;}
  if(add){bl[y]=b.size();b.push_back(y);capB[y]=initial;zeroB+=initial==0;oneB+=initial==1;}
 }
 bool outset(int y){if(al[y]>=0)return false;int avail=0;for(int k=1;k<512;k*=2){int o=y^k;avail+=allowed[o]&&popcount(unsigned(load[o]))<=1;if(avail>=2)return true;}return avail==1&&oneB==0;}
 void dfs(int n,int v){if(local>=limit||won)return;nodes++;local++;if(trie[n].leaf>=0){terms++;P l,r;if(!side(a,load,al,l))return;leftWorks++;if(!side(b,load,bl,r))return;reverse(l.begin(),l.end());l.insert(l.end(),r.begin()+1,r.end());assert(induced(l));won=true;cout<<"JOIN "<<id<<" "<<trie[n].leaf<<" "<<l.size()-1;for(int d:img)cout<<" "<<d;for(int x:l)cout<<" "<<x;cout<<endl;return;}
  for(auto [m,c]:trie[n].next){if(trie[c].maxRank<cutRank)continue;int p=countr_zero(unsigned(m)),q=countr_zero(unsigned(m&(m-1))),f=img[p],g=img[q];unsigned free=511^used;
  for(unsigned ai=f<0?free:(1U<<f);ai;ai&=ai-1){unsigned x=ai&-ai;
  for(unsigned bj=g<0?(free&~x):(1U<<g);bj;bj&=bj-1){unsigned y=bj&-bj;tests++;int dst=v^x^y;if(!outset(dst))continue;toggle(dst,true);
   if(!zeroA&&oneA<=1&&!zeroB&&oneB<=1){if(f<0)img[p]=countr_zero(x),used^=x;if(g<0)img[q]=countr_zero(y),used^=y;dfs(c,dst);if(f<0)img[p]=-1,used^=x;if(g<0)img[q]=-1,used^=y;}
   toggle(dst,false);if(local>=limit||won)return;
  }}}
 }
};
#ifndef PORT_GRAPH_LIBRARY
int main(int argc,char**argv){assert(argc==6);ifstream f(argv[1]),fi(argv[2]);string l;while(getline(f,l)){istringstream in(l);P p;int x;while(in>>x)p.push_back(x);arms.push_back(p);}int x;while(fi>>x)order.push_back(x);rankOf.resize(order.size());for(int j=0;j<order.size();j++)rankOf[order[j]]=j;
 for(int j=0;j<arms.size();j++)put(arms[j],j);int start=stoi(argv[3]),count=stoi(argv[4]);U bound=stoull(argv[5]);int rows=0;
 for(int j=start;j<min(int(order.size()),start+count);j++){int id=order[j];Join a(arms[id],id,j,bound,false);a.dfs(0,0);rows++;capRows+=a.local>=bound;if(won)break;
 if(rows%25==0)cout<<"AT "<<rows<<" "<<nodes<<" "<<tests<<" "<<terms<<" "<<capRows<<endl;}
 cout<<"DONE rows "<<rows<<" nodes "<<nodes<<" assignments "<<tests<<" terminals "<<terms<<" left_solutions "<<leftWorks<<" Hamilton "<<ham<<" unknown "<<unknown<<" caprows "<<capRows<<" hit "<<won<<endl;}

#endif
