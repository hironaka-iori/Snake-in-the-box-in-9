#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
using V=vector<int>;
struct Arc {int s=0,e=0;};
struct Search{
 int p[2][192],at[2][512],used[512]{},nb[512]{},pose=0,threshold=167,minarc=7;
 long long cap=0,steps=0,poses=0,caps=0,starts=0,strict=0,extensions=0,exnodes=0,excaps=0,withPaths=0,exlocal=0,exbudget=5000;
 int maxcore=0,maxfinal=0,side=0; bool control=false,found=false; int bridge=0;
 array<Arc,4> trace; array<int,3> inter{-1,-1,-1}; V walk,left,right;
 struct Link{int dest,bridge;};
 vector<Link> links[2][192];
 set<string> high; ofstream out;
 void mark(int x,int v){used[x]+=v;for(int d=0;d<9;d++)nb[x^(1<<d)]+=v;}
 bool legal(int v){return !used[v]&&nb[v]==1;}
 void push(int x){walk.push_back(x);mark(x,1);}
 void pop(){mark(walk.back(),-1);walk.pop_back();}
 bool reordered(Arc x,Arc y){return (x.e-x.s)*(y.e-y.s)<0 || (x.e-x.s)*(y.s-x.e)<0;}
 void capture(){
    V full(left.rbegin(),left.rend());full.insert(full.end(),walk.begin(),walk.end());full.insert(full.end(),right.begin(),right.end());
    int n=full.size()-1;bool best=n>maxfinal;maxfinal=max(maxfinal,n);
    if(n<189&&!best)return;
    auto norm=[](string w){int m[9],t=0;fill(m,m+9,-1);for(auto& c:w){int j=c-'0';if(m[j]<0)m[j]=t++;c='0'+m[j];}return w;};
    string w;for(int i=1;i<=n;i++)w+=char('0'+countr_zero(unsigned(full[i]^full[i-1])));
    string k=norm(w);reverse(w.begin(),w.end());k=min(k,norm(w));
    if(!high.insert(k).second)return;
    out<<n<<' '<<pose<<' '<<side<<' '<<left.size()<<' '<<right.size();for(auto t:trace)out<<' '<<t.s<<' '<<t.e;
    for(int x:inter)out<<' '<<x;for(int x:full)out<<' '<<x;out<<endl;
    if(n>=192)found=true;
 }
 void extend(int a,int b,bool onLeft){
    if(found||exlocal>=exbudget)return;
    ++exlocal;++exnodes;
    int n=left.size()+right.size()+walk.size()-1;
    if(n>maxfinal||n>=189)capture();
    if(onLeft)extend(a,b,false);
    int tip=onLeft?a:b;
    for(int d=0;d<9;d++){int x=tip^(1<<d);if(!legal(x))continue;
      auto& v=onLeft?left:right;v.push_back(x);mark(x,1);
      extend(onLeft?x:a,onLeft?b:x,onLeft);
      mark(x,-1);v.pop_back();if(found||exlocal>=exbudget)return;}
 }
 void arc(int stage,int s,int dir){
    if(found||steps>=cap)return;
    ++steps;++starts;
    int bank=side^(stage&1),base=walk.size();bool exclusive=false;
    for(int i=s;i>=0&&i<192;i+=dir){
      int x=p[bank][i]; if(!walk.empty()&&!legal(x))break;
      push(x);exclusive|=at[1-bank][x]<0;trace[stage]={s,i};
      if(abs(i-s)+1<minarc||(!exclusive&&!control))continue;
      if(stage==3){
        if(!control&&!reordered(trace[0],trace[2])&&!reordered(trace[1],trace[3]))continue;
        if(bridge>=2 && count_if(inter.begin(),inter.end(),[](int x){return x>=0;})<bridge-1)continue;
        ++strict;int n=walk.size()-1;
        if(n>maxcore)maxcore=n;
        if(n>=threshold && (n%4==0||i+dir<0||i+dir>=192||!legal(p[bank][i+dir]))){
            ++extensions;exlocal=0;extend(walk.front(),walk.back(),true);excaps+=exlocal>=exbudget;
        }
      }else{
        for(auto l:links[bank][i]){
            if(bridge>=2 && l.bridge<0 && stage+1-count_if(inter.begin(),inter.begin()+stage,[](int x){return x>=0;})>4-bridge)continue;
            if(l.bridge>=0){if(!legal(l.bridge))continue;push(l.bridge);}
            if(legal(p[1-bank][l.dest])){
              inter[stage]=l.bridge;
              for(int d:{1,-1})arc(stage+1,l.dest,d);
            }
            if(l.bridge>=0)pop();
            if(found||steps>=cap)break;
        }
      }
      if(found||steps>=cap)break;
    }
    while(int(walk.size())>base)pop();
 }
 void run(int num){
    for(int b=0;b<2;b++){fill(at[b],at[b]+512,-1);for(int i=0;i<192;i++)at[b][p[b][i]]=i;}
    for(int b=0;b<2;b++)for(int i=0;i<192;i++){int x=p[b][i];auto& ls=links[b][i];ls.clear();
      for(int d=0;d<9;d++){int y=x^(1<<d),j=at[1-b][y];
        if(j>=0&&(control||at[1-b][x]<0||at[b][y]<0))ls.push_back({j,-1});
        if(bridge&&at[b][y]<0&&j<0)for(int e=0;e<9;e++){int z=y^(1<<e),k=at[1-b][z];if(k>=0&&z!=x&&(at[1-b][x]<0||at[b][z]<0))ls.push_back({k,y});}
      }
    }
    if(bridge>=2)for(int b=0;b<2;b++)for(auto& ls:links[b])stable_sort(ls.begin(),ls.end(),[](auto x,auto y){return (x.bridge>=0)>(y.bridge>=0);});
    vector<array<int,3>> inits;
    for(int b=0;b<2;b++)for(int trim:{0,1,3,7,13,21,34,55})for(int dir:{1,-1})inits.push_back({b,dir>0?trim:191-trim,dir});
    mt19937 rng(88019+num);shuffle(inits.begin(),inits.end(),rng);bool crossed=false;
    for(auto [b,s,dir]:inits){side=b;steps=0;arc(0,s,dir);crossed|=steps>=cap;if(found)break;}
    caps+=crossed;++poses;
 }
};
int main(int argc,char** argv){
 if(argc!=10)return 2;
 Search z;z.out.open(argv[2]);z.cap=stoi(argv[3]);z.threshold=stoi(argv[4]);z.minarc=stoi(argv[5]);z.control=stoi(argv[6]);z.bridge=stoi(argv[7]);int stride=stoi(argv[8]);int offset=stoi(argv[9]);ifstream in(argv[1]);
 for(int id=0;in>>z.p[0][0];id++){for(int i=1;i<384;i++)in>>z.p[i/192][i%192];if(id%stride!=offset)continue;
  z.pose=id;z.run(id);if(z.found)break;}
 cout<<"poses "<<z.poses<<" capped_poses "<<z.caps<<" starts "<<z.starts<<" strict_or_control_core_prefixes "<<z.strict<<" max_core "<<z.maxcore<<" extension_queries "<<z.extensions<<" extension_nodes "<<z.exnodes<<" capped_extension_queries "<<z.excaps<<" best_edges "<<z.maxfinal<<" saved "<<z.high.size()<<endl;
}
