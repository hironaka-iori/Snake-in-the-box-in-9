#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <set>
using namespace std;
using P=vector<int>;
struct XorDSU{
 int parent[260],par[260]{};
 XorDSU(){for(int i=0;i<260;++i)parent[i]=i;}
 int root(int x){
  if(parent[x]!=x){int a=parent[x];parent[x]=root(a);par[x]^=par[a];}
  return parent[x];
 }
 bool equal(int a,int b,int z){
  int x=root(a),y=root(b); int d=par[a]^par[b]^z;
  if(x==y)return !d;
  parent[x]=y;par[x]=d;return true;
 }
};
int valid(const P&p){for(int j=0;j<(int)p.size();j++)for(int i=0;i<j;i++)if(p[i]==p[j]||((__builtin_popcount(p[i]^p[j])==1)!=(i+1==j)))return 0;return 1;}
struct Run{
 int goal, cap,level,best=-1;
 unsigned long long calls=0,feasible=0,skips=0;
 map<int,long long> hist;set<string> saved; int savebound;
 Run(int a,int b,int c,int d):goal(a),cap(b),level(c),savebound(d){}
 int eval(const P&p){
  ++calls;
  int n=p.size(),pos[256]; fill(pos,pos+256,-1);
  for(int i=0;i<n;i++){if(pos[p[i]]>=0)return -2;pos[p[i]]=i;}
  XorDSU u;
  for(int i=0;i<n;i++)for(int d=0;d<8;d++){int j=pos[p[i]^(1<<d)];
   if(j>i+1&&(!u.equal(i,i+1,0)||!u.equal(j,j+1,0)||!u.equal(i,j,1)))return -1;
  }
  int r[260],fl[260],runs[260]{},idx[260];fill(idx,idx+260,-1);
  for(int i=0;i<=n;i++){r[i]=u.root(i);fl[i]=u.par[i];if(!i||r[i]!=r[i-1])runs[r[i]]++;}
  int k=0;for(int j=0;j<=n;j++)if(runs[j]>1)idx[j]=k++;
  if(k>cap){skips++;return -3;}
  feasible++;
  int mx=-10000;
  for(int mask=0;mask<(1<<max(0,k-1));mask++){
   array<int,4> dp;dp.fill(-10000); unsigned char par[260][4];
   for(int b=0;b<2;b++){
    int j=idx[r[0]];
    if(j<0 || b==(((mask>>j)&1)^fl[0]))dp[2*b]=0;
   }
   for(int i=1;i<=n;i++){
    array<int,4> next;next.fill(-10000);
    for(int a=0;a<4;a++)if(dp[a]>=0)for(int b=0;b<2;b++){
     int j=idx[r[i]];
     if(j>=0&&b!=(((mask>>j)&1)^fl[i]))continue;
     if(r[i]==r[i-1]&&((b^(a>>1))!=(fl[i]^fl[i-1])))continue;
     int f=b^(a>>1);if(f&&(a&1))continue;
     int state=b*2+f; if(dp[a]+f>next[state]){next[state]=dp[a]+f;par[i][state]=a;}
    }
    dp=next;
   }
   int state=max_element(dp.begin(),dp.end())-dp.begin();
   if(dp[state]<0)continue;
   int edges=n-1+dp[state];mx=max(mx,edges);
   if(edges>=goal){
    P labels(n+1);for(int i=n;i>=0;i--){labels[i]=state/2;if(i)state=par[i][state];}
    P w;for(int i=0;i<n;i++){w.push_back(p[i]+256*labels[i]);if(labels[i]!=labels[i+1])w.push_back(p[i]+256*labels[i+1]);}
    assert((int)w.size()==edges+1&&valid(w));
    cout<<"FOUND "<<edges;for(int v:w)cout<<" "<<v;cout<<endl;exit(0);
   }
  }
  hist[mx]++;
  best=max(best,mx);
  if(mx>=savebound){
   string key;int mp[8];fill(mp,mp+8,-1);int cnt=0;
   for(int i=1;i<n;i++){int d=__builtin_ctz(p[i]^p[i-1]); if(mp[d]<0)mp[d]=cnt++;key.push_back('0'+mp[d]);}
   if(saved.insert(key).second)cout<<mx<<" "<<key<<"\n";
  }
  return mx;
 }
 void search(P p){
  int n=p.size(),pos[256];fill(pos,pos+256,-1);for(int i=0;i<n;i++)pos[p[i]]=i;
  eval(p);if(!level)return;
  if(level==2){
   // Reflect a contiguous portion in an axis swap about its first vertex.
   for(int i=0;i<n-1;i++)for(int a=0;a<8;a++)for(int b=0;b<a;b++){
    int mask=(1<<a)|(1<<b);
    auto image=[&](int v){return (__builtin_parity((v^p[i])&mask))?v^mask:v;};
    if(image(p[i+1])==p[i+1])continue;
    int collisions=0;bool prevchanged=false;
    for(int j=i+1;j<n;j++){
     int q=image(p[j]);bool changed=q!=p[j];
     if(changed && pos[q]>=0)collisions+=(pos[q]>=i && pos[q]<j)?-1:1;
     bool last=(j==n-1);
     if(!collisions&&((!changed&&prevchanged)||(changed&&last))){
      P v=p;for(int z=i+1;z<=j;z++)v[z]=image(v[z]);eval(v);
     }
     prevchanged=changed;
    }
   }
   return;
  }
  for(int i=1;i<n-1;i++){
   int q=p[i-1]^p[i]^p[i+1];if(pos[q]<0){swap(q,p[i]);eval(p);swap(q,p[i]);}
  }
  for(int i=0;i<n-1;i++){
   for(int d=0;d<8;d++){int z=1<<d,a=p[i]^z,b=p[i+1]^z;
    if(pos[a]<0&&pos[b]<0){
     P q=p;q.insert(q.begin()+i+1,{a,b});eval(q);
    }else if(pos[a]>i+1&&pos[a]<n-1&&p[pos[a]+1]==b){
     P q=p;reverse(q.begin()+i+1,q.begin()+pos[a]+1);eval(q);
    }
   }
   if(i+3<n&&__builtin_popcount(p[i]^p[i+3])==1){P q=p;q.erase(q.begin()+i+1,q.begin()+i+3);eval(q);}
  }
  for(int s=0;s<2;s++){
   for(int j=0;j<n-2;j++)if(__builtin_popcount(p[j]^p.back())==1){
    P q=p;reverse(q.begin()+j+1,q.end());eval(q);
   }
   for(int d=0;d<8;d++){
    int a=p.back()^(1<<d);if(pos[a]<0){P q=p;q.push_back(a);eval(q);
    for(int e=0;e<8;e++){int b=a^(1<<e);if(pos[b]<0){q.push_back(b);eval(q);q.pop_back();}}}
   }
   reverse(p.begin(),p.end());
  }
 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;
 Run r(stoi(argv[1]),stoi(argv[2]),stoi(argv[3]),stoi(argv[4]));
 string ln;int rows=0;
 while(getline(cin,ln)){if(ln.empty())continue;P p{0};for(char c:ln){if(c<'0'||c>'7')return 4;p.push_back(p.back()^(1<<(c-'0')));}r.search(p);rows++;}
 cerr<<"rows "<<rows<<" calls "<<r.calls<<" parity-consistent "<<r.feasible<<" skips "<<r.skips<<" best "<<r.best<<" saved "<<r.saved.size()<<"\n";for(auto [x,n]:r.hist)if(x>=183)cerr<<x<<":"<<n<<" ";cerr<<endl;
return 0;
}
