// Finite-domain completion: every free Q8 column chooses empty, lower, upper, or both.
#include <algorithm>
#include <array>
#include <iostream>
#include <sstream>
#include <random>
#include <string>
#include <vector>
using namespace std;
using Dom=array<unsigned char,128>;
struct Check {
 array<int,128> base{};array<array<int,4>,128> tips{};
 array<vector<pair<int,int>>,512> adj;
 vector<int> fixed,witness;int needed,limit,nodes=0;bool capped=false;
 Dom domain{};
 Check(const vector<int>&A,int c,int goal,int lim):fixed(A),needed(goal+1-int(A.size())),limit(lim){
  array<bool,512> marked{};for(int v:A)marked[v]=true;
  int j=0;for(int u=0;u<256;u++)if((__builtin_parity(unsigned(u)))!=c){
   base[j]=u;int n[2]={0,0};for(int b=0;b<2;b++){int y=u+256*b;
    for(int d=0;d<8;d++){int x=y^(1<<d);if(marked[x]){++n[b];adj[x].push_back({j,1<<b});}}}
   for(int s=0;s<4;s++){bool ok=true;int t=0;for(int b=0;b<2;b++)if(s&(1<<b)){
    int deg=n[b]+(s==3);ok&=(deg==1||deg==2);t+=(deg==1);}
    if(ok)domain[j]|=1<<s;tips[j][s]=t;}
   ++j;
  }
  for(int x:A)if(marked[x^256])adj[x].push_back({-1,1});
 }
 bool propagate(Dom &v){
  bool changed=true;while(changed){changed=false;
   array<int,128> mx{},mnTip{};int ub=0,globalTips=0;
   for(int j=0;j<128;j++){if(!v[j])return false;mnTip[j]=3;
    for(int s=0;s<4;s++)if(v[j]&(1<<s)){mx[j]=max(mx[j],__builtin_popcount(unsigned(s)));mnTip[j]=min(mnTip[j],tips[j][s]);}
    ub+=mx[j];globalTips+=mnTip[j];}
   if(ub<needed||globalTips>2)return false;
   for(int x:fixed){
    int lo=0,hi=0;for(auto [j,b]:adj[x]){
     if(j<0){++lo;++hi;continue;}int yes=(b==1?10:12);hi+=bool(v[j]&yes);lo+=!(v[j]&~yes);}
    if(lo>2||hi<1)return false;
    globalTips+=(hi==1);if(globalTips>2)return false;
    if(lo==2||hi==1)for(auto [j,b]:adj[x]){if(j<0)continue;int yes=b==1?10:12;
     if((v[j]&yes)&&(v[j]&~yes)){v[j]&=(lo==2?~yes:yes);changed=true;}
    }
   }
   for(int j=0;j<128;j++){for(int s=0;s<4;s++)if(v[j]&(1<<s)){
    if(ub-mx[j]+__builtin_popcount(unsigned(s))<needed||globalTips-mnTip[j]+tips[j][s]>2){
     v[j]&=~(1<<s);changed=true;}
   }if(!v[j])return false;}
  }
  return true;
 }
 bool finish(const Dom &v){
  array<bool,512> used{};for(int x:fixed)used[x]=true;
  for(int j=0;j<128;j++){int s=__builtin_ctz(unsigned(v[j]));for(int b=0;b<2;b++)if(s&(1<<b))used[base[j]+256*b]=true;}
  int n=count(used.begin(),used.end(),true),start=-1,t=0;
  for(int i=0;i<512;i++)if(used[i]){int degree=0;for(int d=0;d<9;d++)degree+=used[i^(1<<d)];
   if(degree==1){start=i;++t;}if(degree<1||degree>2)return false;}
  if(t!=2||n<int(fixed.size())+needed)return false;
  vector<int> p;while(start>=0){int u=start;used[u]=false;p.push_back(u);start=-1;
   for(int d=0;d<9;d++)if(used[u^(1<<d)]){start=u^(1<<d);break;}}
  if(int(p.size())!=n)return false;witness=p;return true;
 }
 bool run(Dom v){
  if(++nodes>limit){capped=true;return false;}if(!propagate(v))return false;
  int j=-1,best=100;for(int z=0;z<128;z++){int b=__builtin_popcount(unsigned(v[z]));if(b>1&&b<best){best=b;j=z;}}
  if(j<0)return finish(v);
  for(int s:{3,1,2,0})if(v[j]&(1<<s)){Dom q=v;q[j]=1<<s;if(run(q))return true;if(capped)return false;}
  return false;
 }
};
int main(int argc,char**argv){
 if(argc!=4)return 2;int goal=stoi(argv[1]),limit=stoi(argv[2]),changes=stoi(argv[3]);string line;
 if(changes<0||changes>2)return 2;
 while(getline(cin,line)){istringstream in(line);int id,c,x;in>>id>>c;vector<int>A;while(in>>x)A.push_back(x);
  vector<int> slots;for(int v=0;v<512;v++)if(__builtin_parity(unsigned(v%256))==c)slots.push_back(v);
  std::mt19937 rng(15577+id);
  int checked=0,open=0;long long nodes=0;vector<pair<int,int>> jobs;
  if(!changes)jobs.push_back({-1,-1});
  else if(changes==1)for(int v:slots)jobs.push_back({v,-1});
  else{std::shuffle(slots.begin(),slots.end(),rng);for(int k=0;k<128;k++)jobs.push_back({slots[2*k],slots[2*k+1]});}
  for(auto [v,w]:jobs){
   auto T=A;
   for(int z:{v,w})if(z>=0){auto it=find(T.begin(),T.end(),z);if(it==T.end())T.push_back(z);else T.erase(it);}
   Check test(T,c,goal,limit);bool found=test.run(test.domain);nodes+=test.nodes;++checked;
   if(found){cout<<"FOUND "<<id<<" "<<v;if(changes==2)cout<<" "<<w;for(int z:test.witness)cout<<" "<<z;cout<<endl;return 0;}
   if(test.capped){cout<<"UNKNOWN "<<id<<" "<<v;if(changes==2)cout<<" "<<w;cout<<"\n";++open;}
  }
  cout<<"DONE "<<id<<" "<<checked<<" "<<open<<" "<<nodes<<endl;
 }return 0;}
