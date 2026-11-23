#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
int wt(int x){return popcount(unsigned(x));}
struct Connector {
 array<int,512> ban{},fixed{},degree{};vector<int> q;int src,dst,H;
 bool dfs(int x,int depth){
  if(depth==H-1)return wt(x^dst)==1;
  ban[x]++;for(int j=0;j<9;++j)ban[x^(1<<j)]++;
  for(int j=0;j<9;++j){int y=x^(1<<j);if(fixed[y]||ban[y]>1||wt(y^dst)>H-depth-1)continue;
   if(degree[y]!=int(depth+1==1)+int(depth+1==H-1))continue;
   if((wt(y^src)==1)!=(depth+1==1)||(wt(y^dst)==1)!=(depth+1==H-1))continue;
   q.push_back(y);if(dfs(y,depth+1))return true;q.pop_back();
  }
  ban[x]--;for(int j=0;j<9;++j)ban[x^(1<<j)]--;return false;
 }
 bool valid(const vector<int>&p){for(int i=0;i<p.size();++i)for(int j=0;j<i;++j)if(p[i]==p[j]||(wt(p[i]^p[j])==1)!=(i==j+1))return false;return true;}
};
int main(int argc,char**argv){
 vector<vector<int>> paths;string w;while(cin>>w){vector<int>p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));paths.push_back(p);}
 int mx=stoi(argv[1]),mn=stoi(argv[2]);long long count=0,feasible=0;
 for(int goal=mx;goal>=mn;--goal){
  for(int row=0;row<paths.size();++row){auto &p=paths[row];int n=p.size();
   for(int d=0;d<9;++d){vector<int> flips{-1};for(int k=0;k+1<n;++k)if((p[k]^p[k+1])==(1<<d))flips.push_back(k);flips.push_back(n-1);
    for(int k=1;k+1<flips.size();++k){
     int pivot=flips[k],lo=flips[k-1]+1,hi=flips[k+1];if(hi-lo+12<goal)continue;
     for(int t=1;t<512;++t){if(t>>d&1)continue;int h=wt(t)+1;
      for(int e:{2,4}){
       int span=goal-(h-1)-e;
       for(int a=max(lo,pivot+1-span);a<=min(pivot,hi-span);++a){int b=a+span;++count;
        vector<int>c;Connector z;bool good=true;
        for(int u=a;u<=b;++u){int v=p[u]^(p[u]>>d&1?t:0);int exp=(u>a&&u!=pivot+1);if(z.fixed[v]||z.degree[v]!=exp){good=false;break;}
         z.fixed[v]=1;for(int j=0;j<9;++j)++z.degree[v^(1<<j)];c.push_back(v);}
        if(!good)continue;++feasible;int ix=pivot-a;z.src=c[ix];z.dst=c[ix+1];z.H=h+e;
        if(z.dfs(z.src,0)){vector<int>ans(c.begin(),c.begin()+ix+1);ans.insert(ans.end(),z.q.begin(),z.q.end());ans.insert(ans.end(),c.begin()+ix+1,c.end());
         if(ans.size()!=goal+1||!z.valid(ans))abort();
         cout<<"FOUND "<<goal<<" "<<row<<" "<<d<<" "<<t<<" "<<a<<" "<<b<<" "<<pivot<<" "<<e<<" "<<count<<" "<<feasible;for(int v:ans)cout<<" "<<v;cout<<endl;return 0;}
       }
      }
     }
    }
   }
  }cout<<"EXHAUSTED "<<goal<<" "<<count<<" "<<feasible<<endl;
 }
}
