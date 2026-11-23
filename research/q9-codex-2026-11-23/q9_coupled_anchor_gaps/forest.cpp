#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <numeric>
#include <random>
#include <set>
#include <vector>
using namespace std;
struct Pair{int x,y;};
Pair ports(int a,int b){int d=a^b;int x=d&-d;return {a^x,b^x};}
int weight(int v){return __builtin_popcount((unsigned)v);}
struct Gap{int l,r,n;bool back;vector<int> fill;};
struct Solver{
 int tips;vector<int> ref,e;vector<Gap> g;vector<Pair> edges;vector<int> order,w;
 array<int,512> used{},load{};vector<int> masks;int budget,vis=0;bool init=false,capped=false;
 Solver(vector<int> data,vector<int> orig,vector<Gap> gaps,int cap,int addtips,mt19937& rng):tips(addtips),ref(orig),e(data),g(gaps),budget(cap){
  for(int d=1;d<512;++d)if(weight(d)==2)masks.push_back(d);
  shuffle(masks.begin(),masks.end(),rng);
  vector<int> keep(e.size(),1);for(auto &x:g)for(int j=x.l;j<=x.r;j++)keep[j]=0;
  for(int j=0;j<(int)e.size();j++)if(keep[j]){
   if(used[e[j]])return;
   mark(e[j],1);
   if(j&&keep[j-1]){if(weight(e[j]^e[j-1])!=2)return;edges.push_back(ports(e[j],e[j-1]));}
  }
  init=valid();for(int i=0;i<(int)g.size();i++)order.push_back(i);
  shuffle(order.begin(),order.end(),rng);
  stable_sort(order.begin(),order.end(),[&](int a,int b){return g[a].n<g[b].n;});
 }
 void mark(int a,int delta){used[a]+=delta;for(int j=0;j<9;j++)load[a^(1<<j)]+=delta;}
 bool valid(){for(auto p:edges)if(load[p.x]>2&&load[p.y]>2)return false;return true;}
 bool finish(){
  vector<int> v;int pos=0;
  for(auto &x:g){while(pos<x.l)v.push_back(e[pos++]);auto f=x.fill;if(x.back)reverse(f.begin(),f.end());v.insert(v.end(),f.begin(),f.end());pos=x.r+1;}
  while(pos<(int)e.size())v.push_back(e[pos++]);
  array<bool,2> lost{};int mid=(int)e.size()/2;
  for(int i=0;i<(int)ref.size();i++)if(!used[ref[i]])lost[i>=mid]=true;
  if(!lost[0]||!lost[1])return false;
  w.clear();w.push_back(v.front());for(int i=1;i<(int)v.size();i++){
   auto p=ports(v[i-1],v[i]);int odd=load[p.x]==2?p.x:p.y;
   if(weight(v[i-1]^v[i])!=2||load[odd]!=2)abort();
   w.push_back(odd);w.push_back(v[i]);}
  if(tips){
   int left=-1,right=-1;for(int d=0;d<9;d++){int a=v.front()^(1<<d),b=v.back()^(1<<d);
    if(load[a]==1)left=a;if(load[b]==1)right=b;}
   if(tips==2&&(left<0||right<0))return false;
   if(tips==1&&left<0&&right<0)return false;
   if(left>=0)w.insert(w.begin(),left);
   if(right>=0&&(tips==2||left<0))w.push_back(right);
  }
  return true;
 }
 bool dfs(int stage,int head,int dest,int remain){
  if(vis>=budget){capped=true;return false;}vis++;
  if(dest>=0&&weight(head^dest)>2*(remain+1))return false;
  if(remain==0){
   if(dest>=0){if(weight(head^dest)!=2)return false;auto p=ports(head,dest);
    if(load[p.x]>2&&load[p.y]>2)return false;
    edges.push_back(p);}
   bool ok=next(stage+1);if(dest>=0)edges.pop_back();return ok;
  }
  for(int d:masks){int v=head^d;if(used[v]||(dest>=0&&weight(v^dest)>2*remain))continue;
   auto p=ports(head,v);if(load[p.x]>=2&&load[p.y]>=2)continue;
   mark(v,1);edges.push_back(p);bool ok=false;
   if(valid()){auto &f=g[order[stage]].fill;f.push_back(v);ok=dfs(stage,v,dest,remain-1);f.pop_back();}
   edges.pop_back();mark(v,-1);if(ok)return true;if(capped)break;
  }return false;
 }
 bool next(int stage){
  if(stage==(int)order.size())return finish();
  auto &x=g[order[stage]];int a=x.l?e[x.l-1]:-1,b=x.r+1<(int)e.size()?e[x.r+1]:-1;
  if(x.back)swap(a,b);if(a<0)abort();return dfs(stage,a,b,x.n);
 }
};
int main(int argc,char**argv){
 if(argc!=6)return 2;
 int mode=atoi(argv[1]),rounds=atoi(argv[2]),cap=atoi(argv[3]),target=atoi(argv[4]);mt19937 rng(atoi(argv[5]));
 auto randn=[&](int n){return (int)(rng()%(unsigned)n);};
 long long total=0,ready=0,nodes=0,caps=0,hit=0;int typ,id,np;
 while(cin>>typ>>id>>np){vector<int> p(np);for(int &v:p)cin>>v;
  if((mode==0||mode==3||mode==5||mode==7||mode==10||mode==12)?typ!=0:typ!=1)continue;
  for(int flip=0;flip<(typ?2:1);flip++){
   vector<int> e;for(int j=flip;j<np;j+=2)e.push_back(p[j]);
   int n=e.size(),mid=n/2;set<pair<int,int>> rr;
   vector<int> focus[2];array<int,512> deg{};for(int v:e)for(int j=0;j<9;j++)deg[v^(1<<j)]++;
   for(int i=1;i<n;i++){
    auto q=ports(e[i-1],e[i]);if(deg[q.x]<=2||deg[q.y]<=2)continue;
    for(int j=0;j<n;j++)if(weight(e[j]^q.x)==1||weight(e[j]^q.y)==1)focus[j>=mid].push_back(j);
   }
   set<vector<int>> unique;
   for(int k=0;k<rounds;k++){
    vector<int> work=e;vector<Gap> g;int missing=0;bool poisonOK=true;
    auto interval=[&](int l,int r){int side=l>=mid;int center;
     if(mode==2||mode==9)center=l+2+randn(r-l-3);
     else if(!focus[side].empty()&&randn(5))center=focus[side][randn(focus[side].size())];
     else {int type=randn(5);center=type==0?(side?r:l):type==1?(side?l:r):l+randn(r-l+1);}
     int size=(mode==2||mode==9)?1+randn(3):1+randn(k%4==0?13:7);int a=max(l,min(r-size+1,center-randn(size))),b=a+size-1;
     if(mode==2){work[a]=e[a]^1;}
     if(mode==9){bool broken=false;
      for(int j=max(1,a);j<=min(n-2,b)&&!broken;j++){
       for(int x=0;x<512&&!broken;x++)if(weight(x^e[j-1])==2&&weight(x^e[j+1])==2&&find(e.begin(),e.end(),x)==e.end()&&find(work.begin(),work.end(),x)==work.end()){
        vector<int> check=e;check[j]=x;array<int,512> count{};
        for(int v:check)for(int d=0;d<9;d++)count[v^(1<<d)]++;
        for(int h=1;h<n;h++){auto pp=ports(check[h-1],check[h]);if(count[pp.x]>2&&count[pp.y]>2){work[j]=x;broken=true;break;}}
       }
      }
      poisonOK&=broken;
     }
     g.push_back({a,b,size,(bool)randn(2),{}});missing+=size;
    };
    interval(0,mid-2);interval(mid+1,n-1);if(!poisonOK)continue;
    if(mode!=2&&mode!=9&&k%3!=0){
     vector<int> holes;for(int i=1;i<n-1;i++)if((i<g[0].l-1||i>g[0].r+1)&&(i<g[1].l-1||i>g[1].r+1))holes.push_back(i);
     if(!holes.empty()){
      int c=holes[randn(holes.size())];if(k%3==1)c=mid;
      int a=c,b=c;if(c>g[0].r+1&&c<g[1].l-1){a=max(g[0].r+2,c-randn(4));b=min(g[1].l-2,c+randn(4));}
      if(a<=b&&(a>g[0].r+1||b<g[0].l-1)&&(a>g[1].r+1||b<g[1].l-1))g.push_back({a,b,b-a+1,(bool)randn(2),{}});
     }
    }
    sort(g.begin(),g.end(),[](auto a,auto b){return a.l<b.l;});
    int transform=0,tx=0,axisA=0,axisB=0;
    vector<int> recipe;
    if(mode>=10){
     if(g[0].l==0||g.back().r==n-1)continue;
     vector<vector<int>> pieces;int start=0;
     for(auto& h:g){
      pieces.emplace_back(e.begin()+start,e.begin()+h.l);start=h.r+1;
      recipe.push_back(h.l);recipe.push_back(h.r);
     }
     pieces.emplace_back(e.begin()+start,e.end());
     vector<int> perm(pieces.size());iota(perm.begin(),perm.end(),0);shuffle(perm.begin(),perm.end(),rng);
     if(perm.front()>perm.back())reverse(perm.begin(),perm.end());
     work.clear();
     for(int j=0;j<(int)perm.size();j++){
      int idx=perm[j],rev=randn(2);if(rev)reverse(pieces[idx].begin(),pieces[idx].end());recipe.push_back(2*idx+rev);
      work.insert(work.end(),pieces[idx].begin(),pieces[idx].end());
      if(j<(int)g.size()){
       int size=g[j].r-g[j].l+1;g[j].l=work.size();g[j].r=g[j].l+size-1;
       work.insert(work.end(),size,0);
      }
     }
    }

    if(mode>=3&&mode<=6){
     int from=g.front().r+1,to=g.back().l-1;
     if(from>to)continue;
     transform=1+randn(4);axisA=randn(9);axisB=randn(8);if(axisB>=axisA)axisB++;
     tx=work[from+randn(to-from+1)];
     int mask=(1<<axisA)|(1<<axisB);
     for(int i=from;i<=to;i++){
      int base=work[i]^tx;
      if(transform<4&&((base>>axisA)^(base>>axisB))&1)work[i]^=mask;
      if(transform>=3)work[i]^=mask;
     }
     if(work==e)continue;
    }
    int tips=target%2?1:(mode==3||mode==4||mode==7||mode==8||mode==12||mode==13?2:0);
    int diff=(target-tips)/2+1-n;g[randn(g.size())].n+=diff;
    if(mode!=2&&mode!=9&&randn(3)){int a=randn(g.size()),b=randn(g.size());int t=1+randn(2);g[a].n-=t;g[b].n+=t;}
    vector<int> key;bool good=true;for(auto &x:g){if(x.n<0)good=false;if(!x.l)x.back=true;if(x.r==n-1)x.back=false;key.insert(key.end(),{x.l,x.r,x.n});}
    key.insert(key.end(),recipe.begin(),recipe.end());if(transform)key.insert(key.end(),{transform,axisA,axisB,((tx>>axisA)^(tx>>axisB))&1});if(!good||!unique.insert(key).second)continue;
    Solver s(work,mode==2||mode==9?work:e,g,cap,tips,rng);total++;if(!s.init)continue;ready++;
    bool found=s.next(0);nodes+=s.vis;caps+=s.capped;
    if(found){hit++;if(mode==9){cout<<"C "<<id<<" "<<flip<<" "<<k;for(int j=0;j<n;j++)if(work[j]!=e[j])cout<<" "<<j<<" "<<work[j];cout<<"\n";}{cout<<"W "<<id<<" "<<flip<<" "<<target<<" "<<k;for(int v:s.w)cout<<" "<<v;cout<<"\n";}
     if(target>=192){cout<<"FOUND\n";return 0;}}
   }
  }
  cout<<"COUNT "<<id<<" "<<total<<" "<<ready<<" "<<nodes<<" "<<caps<<" "<<hit<<endl;
 }
}
