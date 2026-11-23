#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <vector>
using namespace std;mt19937 eng(373989);
int main(int argc,char**argv){assert(argc==3);ifstream f(argv[1]);int cap=stoi(argv[2]),global=0,total=0,reachable=0,probes=0;long long explored=0;string w;
 for(int k=0;f>>w;k++){vector<int>A{0};for(char c:w)A.push_back(A.back()^(1<<(c-'0')));array<char,256>don{};for(int v:A)don[v]=1;
  for(int x=0;x<256;x++){bool isolated=!don[x];for(int d=0;d<8;d++)if(don[x^(1<<d)])isolated=false;if(!isolated)continue;total++;
   for(int orient=0;orient<2;orient++){auto arm=A;if(orient)reverse(arm.begin(),arm.end());int t=arm.front(),u=arm.back();
    for(int rep=0;rep<2;rep++){array<int,256>p;p.fill(-1);p[x]=x;vector<int>q{x};array<int,8>axes; iota(axes.begin(),axes.end(),0);shuffle(axes.begin(),axes.end(),eng);
     for(int at=0;at<q.size()&&p[t]<0;at++)for(int z:axes){int v=q[at]^(1<<z);if(p[v]>=0||(don[v]&&v!=t)||popcount(unsigned(u^v))<=1)continue;p[v]=q[at];q.push_back(v);}
     if(p[t]<0)continue;reachable++;vector<int>connector{t};while(connector.back()!=x)connector.push_back(p[connector.back()]);reverse(connector.begin(),connector.end());
     array<int,256>deny{};for(int v=0;v<256;v++)if(don[v]&&v!=u)deny[v]=1;
     for(int v:connector){deny[v]++;for(int d=0;d<8;d++)deny[v^(1<<d)]++;}if(deny[u])continue;
     vector<int>left{u};int fuel=cap;
     auto search=[&](auto&&rec,int v)->void{
      fuel--;explored++;int edges=1+connector.size()+arm.size()+left.size()-1;
      if(edges%2==1&&edges>global){vector<int> path{x};for(int z:connector)path.push_back(z+256);path.insert(path.end(),arm.begin(),arm.end());for(int z:left)path.push_back(z+256);
       assert(path.size()==edges+1);for(int i=0;i<path.size();i++)for(int j=0;j<i;j++)assert(path[i]!=path[j]&&((popcount(unsigned(path[i]^path[j]))==1)==(i==j+1)));
       cout<<"WIT "<<edges<<" "<<k<<" "<<x;for(int z:path)cout<<" "<<z;cout<<endl;global=edges;
      }
      array<int,8>ds=axes;shuffle(ds.begin(),ds.end(),eng);vector<int>ns;for(int d:ds){int y=v^(1<<d);if(!deny[y])ns.push_back(y);}
      deny[v]++;for(int d:axes)deny[v^(1<<d)]++;
      for(int y:ns){if(fuel<=0)break;left.push_back(y);rec(rec,y);left.pop_back();}
      deny[v]--;for(int d:axes)deny[v^(1<<d)]--;
     };
     probes++;search(search,u);
    }
   }
  }
 }cout<<"DONE "<<total<<" geometries "<<reachable<<" bridges "<<probes<<" DFS searches "<<explored<<" nodes best "<<global<<"\n";
}
