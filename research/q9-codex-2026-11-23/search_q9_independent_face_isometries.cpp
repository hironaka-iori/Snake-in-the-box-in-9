// Independently relabel the inner coordinates of each parallel cube face.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Map=array<unsigned char,128>;
struct Link {int a,b; vector<int> pins;};
struct Opt {int perm, shift;};
struct FaceSearch {
 int dim,sz,faces,cap,nodes=0; bool limited=false;const vector<Map>& maps; 
 vector<int> outer,inner; vector<vector<int>> occupied; vector<array<unsigned char,128>> has, image;
 vector<vector<int>> cross;vector<Link> edges; vector<int> order,parent;vector<vector<Opt>> options; vector<Map> placement;
 FaceSearch(int d,const vector<Map>& m,int limit):dim(d),sz(1<<d),faces(512/sz),cap(limit),maps(m),occupied(faces),has(faces),image(faces),cross(faces,vector<int>(faces)),parent(faces,-1),options(faces),placement(faces){}
 int run(const vector<int>& path,int mask,vector<int>& solution){
  for(int v:path){int a=0,b=0,ai=1,bi=1;
   for(int d=0;d<9;d++)if(mask>>d&1){if(v>>d&1)a|=ai;ai*=2;}else{if(v>>d&1)b|=bi;bi*=2;}
   outer.push_back(a);inner.push_back(b);occupied[a].push_back(b);has[a][b]=1;
  }
  vector<vector<vector<int>>> pins(faces,vector<vector<int>>(faces));
  for(size_t i=1;i<path.size();i++){int a=outer[i-1],b=outer[i];if(a==b)continue;
   if(inner[i]!=inner[i-1])abort();
   pins[a][b].push_back(inner[i]);pins[b][a].push_back(inner[i]);cross[a][b]++;cross[b][a]++;
  }
  for(int a=0;a<faces;a++)for(int b=0;b<a;b++)if(cross[a][b])edges.push_back({a,b,pins[a][b]});
  sort(edges.begin(),edges.end(),[](auto &a,auto &b){return a.pins.size()>b.pins.size();});
  vector<char> placed(faces);int root=edges.empty()?outer[0]:edges[0].a;placed[root]=true;order.push_back(root);
  for(;;){int best=-1,mindom=10000000;
   for(size_t i=0;i<edges.size();i++){
    auto &e=edges[i];if(placed[e.a]==placed[e.b])continue;
    int pin=e.pins[0], classes[128]={},width=0;
    for(int j=0;j<dim;j++){int signature=0; // equivalent columns can be permuted freely.
     for(int k=0;k<j;k++){bool eq=true;for(int v:e.pins)if((((v^pin)>>j)^((v^pin)>>k))&1){eq=false;break;}if(eq){signature=classes[k];break;}}
     classes[j]=signature?signature:++width;
    }
    int ways=1;for(int k=0;k<dim;k++){int num=1;for(int j=0;j<k;j++)if(classes[j]==classes[k])num++;ways*=num;}
    if(ways<mindom){mindom=ways;best=i;}
   }
   if(best<0)break;auto &e=edges[best];int a=placed[e.a]?e.a:e.b,b=a==e.a?e.b:e.a;
   int pin=e.pins[0];for(size_t pi=0;pi<maps.size();pi++){
    auto &p=maps[pi];int sh=p[pin]^pin;bool ok=true;for(int x:e.pins)if((p[x]^sh)!=x){ok=false;break;}if(!ok)continue;
    int contacts=0;for(int x:occupied[b])contacts+=has[a][p[x]^sh];
    if(contacts==(int)e.pins.size())options[b].push_back({(int)pi,sh});
   }
   if(options[b].empty())return 0;
   parent[b]=a;placed[b]=true;order.push_back(b);
  }
  int used=0;for(auto&v:occupied)used+=!v.empty();if(used!=(int)order.size())abort();
  fill(placed.begin(),placed.end(),false);placed[root]=true;for(int i=0;i<sz;i++)placement[root][i]=i;
  image[root]=has[root]; 
  auto recurse=[&](auto&& self,int idx)->bool {
   if(idx==(int)order.size())return true;int b=order[idx],a=parent[b];for(auto opt:options[b]){
    if(++nodes>cap){limited=true;return false;}
    auto &perm=maps[opt.perm];auto &p=placement[b];for(int x=0;x<sz;x++)p[x]=placement[a][perm[x]^opt.shift];
    bool ok=true;for(int c=0;c<faces&&ok;c++)if(c!=a&&placed[c]&&__builtin_popcount((unsigned)(c^b))==1){
     for(int x:pins[b][c])if(p[x]!=placement[c][x]){ok=false;break;}
     if(ok){int n=0;for(int x:occupied[b])n+=image[c][p[x]];ok=n==cross[b][c];}
    }
    if(!ok)continue;image[b].fill(0);for(int x:occupied[b])image[b][p[x]]=1;placed[b]=true;
    if(self(self,idx+1))return true;placed[b]=false;if(limited)return false;
   }return false;};
  if(!recurse(recurse,1))return limited?-1:0;
  for(size_t i=0;i<outer.size();i++)solution.push_back((outer[i]<<dim)|placement[outer[i]][inner[i]]);
  for(size_t i=0;i<solution.size();i++)for(size_t j=0;j<i;j++)if(solution[i]==solution[j]||(__builtin_popcount((unsigned)(solution[i]^solution[j]))==1)!=(j+1==i))abort();
  return 1;
 }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;int dim=atoi(argv[1]),cap=atoi(argv[2]),seed=atoi(argv[3]),limit=atoi(argv[4]);if(dim<2||dim>7)return 2;
 vector<Map> perms;vector<int> perm(dim);iota(perm.begin(),perm.end(),0);
 do{Map m{};for(int v=1;v<(1<<dim);v++){int d=__builtin_ctz((unsigned)v);m[v]=m[v^(1<<d)]^(1<<perm[d]);}perms.push_back(m);}while(next_permutation(perm.begin(),perm.end()));
 mt19937 rng(seed);vector<vector<int>> bank;string line;
 while(getline(cin,line)){istringstream f(line);vector<int> p;int x;while(f>>x)p.push_back(x);if(!p.empty())bank.push_back(p);}
 shuffle(bank.begin(),bank.end(),rng);long long attempts=0,dead=0,unknown=0,states=0;int completed=0;
 for(auto &p:bank){int required=0;for(size_t i=0;i<p.size();i++)for(size_t j=0;j<i;j++){
  int x=p[i]^p[j];if(!x||p[i]>=512||p[i]<0)abort();if(j+1==i){if(__builtin_popcount((unsigned)x)!=1)abort();}else if(__builtin_popcount((unsigned)x)==1)required|=x;
 }
 vector<int> masks;for(int m=0;m<512;m++)if((m&required)==required&&__builtin_popcount((unsigned)m)==9-dim)masks.push_back(m);shuffle(masks.begin(),masks.end(),rng);
 for(int m:masks){FaceSearch s(dim,perms,cap);vector<int>w;int ans=s.run(p,m,w);attempts++;states+=s.nodes;
  if(ans==1){cout<<"FOUND "<<w.size()-1<<" mask "<<m<<" vertices";for(int v:w)cout<<" "<<v;cout<<endl;return 0;} if(ans<0)unknown++;else dead++;
 }
 completed++;if(completed%25==0)cout<<"progress "<<completed<<" "<<attempts<<" "<<dead<<" "<<unknown<<" "<<states<<endl;if(limit&&completed>=limit)break;
 }cout<<"DONE "<<completed<<" "<<attempts<<" "<<dead<<" "<<unknown<<" "<<states<<endl;
}
