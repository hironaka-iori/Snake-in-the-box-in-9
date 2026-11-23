#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <numeric>
#include <queue>
#include <vector>
using namespace std;
using V=vector<int>;
int wt(int v){return popcount(unsigned(v));}
array<V,512> subsets;
array<array<int,9>,512> adj;
struct End{int x,d;};
vector<End> ends(int v,int m,const array<int,512>&hit,const array<bool,512>&occupied){
 vector<End> p{{v,0}};
 for(int d:subsets[m])if(d&&d!=m){
  int x=v^d,n=wt(d);if(!occupied[x]&&hit[x]==(n==1))p.push_back({x,n});}
 return p;
}
int probe(const V&p,int begin,int end,const array<int,512>&hit,const array<bool,512>&used){
 vector<V> choices;
 for(int i=begin;i<end;++i){
  int a=p[i],b=p[i+1],h=wt(a^b);if(h==1)continue;
  auto walk=[&](int src,int dst){
   vector<V> level(h+1);level[0]={src};
   array<bool,512> seen{};seen[src]=true;
   for(int rank=1;rank<h;++rank){
    for(int x:level[rank-1])for(int y:adj[x]){
     if(seen[y]||used[y]||wt(y^dst)!=h-rank||hit[y]!=(rank==1)+(h-rank==1))continue;
     seen[y]=true;level[rank].push_back(y);
    }
    if(level[rank].empty())break;
   }return level;
  };
  auto left=walk(a,b);if(left[h-1].empty())return 1;auto right=walk(b,a);
  for(int z=1;z<h;++z){V opts;for(int x:left[z])if(find(right[h-z].begin(),right[h-z].end(),x)!=right[h-z].end())opts.push_back(x);
    if(opts.empty())return 1;choices.push_back(move(opts));}
 }
 stable_sort(choices.begin(),choices.end(),[](auto&a,auto&b){return a.size()<b.size();});
 array<int,512> owner;owner.fill(-1);V assigned(choices.size(),-1);
 for(int i=0;i<choices.size();++i){V todo{i};array<int,512> from;from.fill(-1);int last=-1;
  for(int j=0;j<todo.size()&&last<0;++j){int item=todo[j];
   for(int v:choices[item])if(from[v]<0){from[v]=item;if(owner[v]<0){last=v;break;}todo.push_back(owner[v]);}}
  if(last<0)return 2;
  while(last>=0){int item=from[last],old=assigned[item];owner[last]=item;assigned[item]=last;last=old;}
 }
 return 0;
}
int main(int argc,char**argv){
 for(int v=0;v<512;++v)for(int d=0;d<9;++d)adj[v][d]=v^(1<<d);
 for(int m=0;m<512;++m)for(int s=0;s<512;++s)if((s&m)==s)subsets[m].push_back(s);
 bool integral=argc==4;int target=stoi(argv[1]);ofstream out(argv[2]);string w;
 for(int row=0;cin>>w;++row){
  int n=w.size()+1;V orig(n);for(int i=1;i<n;++i)orig[i]=orig[i-1]^(1<<(w[i-1]-'0'));
  array<long long,7> hist{};
  for(int axis=0;axis<9;++axis)for(int shift=1;shift<512;++shift){if(shift>>axis&1)continue;hist[0]++;
   V p(n),cost(n),mask(n+1),upto(n);array<int,512> next;next.fill(n);
   for(int i=0;i<n;++i){p[i]=orig[i]^(orig[i]&(1<<axis)?shift:0);if(i){mask[i]=p[i]^p[i-1];cost[i]=cost[i-1]+wt(mask[i]);}}
   for(int i=n-1;i>=0;--i){
    int fence=i==n-1?n:upto[i+1];fence=min(fence,next[p[i]]);
    for(int u:adj[p[i]])if(next[u]!=i+1)fence=min(fence,next[u]);upto[i]=fence;next[p[i]]=i;
   }
   for(int a=0;a<n-1;++a){
    int capL=max(0,wt(mask[a])-1),capmax=wt(shift);
    int low=lower_bound(cost.begin()+a+1,cost.begin()+upto[a],cost[a]+target-(integral?0:capL+capmax))-cost.begin();
    for(int j=low;j<upto[a]&&cost[j]-cost[a]<target+int(integral);++j){
     int remain=target-cost[j]+cost[a],capR=max(0,wt(mask[j+1])-1);if(remain>capL+capR)continue;
     ++hist[1];array<int,512> hits{};array<bool,512> present{};
     for(int i=a;i<=j;++i){present[p[i]]=true;for(int u:adj[p[i]])++hits[u];}
     auto L=ends(p[a],mask[a],hits,present),R=ends(p[j],mask[j+1],hits,present);int count=0;
     for(auto x:L)for(auto y:R)if(x.d+y.d==remain&&wt(x.x^y.x)>=2)++count;
     hist[2]+=count;
     if(count){int code=probe(p,a,j,hits,present);if(code)hist[2+code]+=count;
      else{++hist[5];hist[6]+=count;out<<row<<" "<<axis<<" "<<shift<<" "<<a<<" "<<j<<" "<<count<<"\n";}}
    }
   }
  }cout<<row;for(long long z:hist)cout<<" "<<z;cout<<endl;
 }
}
