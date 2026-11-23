// Join two disjoint induced Q8 paths placed on opposite layers. Enumerate every
// Q9 bridge up to a specified detour beyond Hamming distance between the ports.
#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using Mask=std::bitset<512>;
using Path=std::vector<int>;
std::array<Mask,512> neighbors;
unsigned long long nodes=0,attempts=0,capped=0,cap;
int target,slack;
bool valid(const Path &p){
 for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++)
  if(p[i]==p[j]||((__builtin_popcount(unsigned(p[i]^p[j]))==1)!=(j==i-1)))return false;
 return true;
}
bool dfs(int s,int goal,int edges,Mask avail,Path& bridge,unsigned long long& n){
 if(__builtin_popcount(unsigned(s^goal))>edges||n>=cap)return false;
 n++;nodes++;
 if(edges==1){if(neighbors[s][goal]){bridge.push_back(goal);return true;}return false;}
 if(neighbors[s][goal])return false;
 auto nextAvail=avail & ~neighbors[s];nextAvail.reset(s);
 for(int d=0;d<9;d++){
  int v=s^(1<<d);
  if(!avail[v]||v==goal)continue;
  bridge.push_back(v);
  if(dfs(v,goal,edges-1,nextAvail,bridge,n))return true;
  bridge.pop_back();
 }
 return false;
}
void search(const Path& a,const Path& b){
 Mask allowed;allowed.set();
 for(auto p:{&a,&b}){
  for(int i=1;i<(int)p->size();i++){int v=(*p)[i];allowed.reset(v);allowed&=~neighbors[v];}
 }
 int s=a.front(),t=b.front();
 int dist=__builtin_popcount(unsigned(s^t));
 int min=std::max(1,target-int(a.size()+b.size()-2));
 int n0=std::max(min,dist);
 if((n0-dist)%2)n0++;
 if(n0>min+slack || n0>dist+slack)return;
 attempts++;
 unsigned long long n=0;
 for(int e=n0;e<=min+slack && e<=dist+slack;e+=2){
  Path q={s};if(!dfs(s,t,e,allowed,q,n))continue;
  Path full(a.rbegin(),a.rend());full.insert(full.end(),q.begin()+1,q.end());full.insert(full.end(),b.begin()+1,b.end());
  if(!valid(full)){std::cerr<<"invalid candidate\n";exit(5);}
  if((int)full.size()<=target)exit(6);
  std::cout<<"FOUND "<<full.size()-1;for(auto v:full)std::cout<<' '<<v;std::cout<<std::endl;exit(0);
 }
 if(n>=cap)++capped;
}

int main(int argc,char**argv){
 if(argc!=6)return 2;
 target=atoi(argv[1]);int trim=atoi(argv[2]);slack=atoi(argv[3]);cap=atoll(argv[4]);int stride=atoi(argv[5]);
 for(int v=0;v<512;v++)for(int d=0;d<9;d++)neighbors[v].set(v^(1<<d));
 int na,nb;std::cin>>na;Path A(na);for(int &v:A)std::cin>>v;std::cin>>nb;Path B(nb);for(int &v:B)std::cin>>v;
 if(!valid(A)||!valid(B))return 3;
 std::array<int,8> pi{0,1,2,3,4,5,6,7};long long images=0,partial=0;int perms=0;
 do{
  if(perms++%stride)continue;
  std::array<int,256> image{};for(int v=1;v<256;v++)image[v]=image[v&(v-1)]^(1<<pi[__builtin_ctz(v)]);
  for(int sa:{0,1})for(int sb:{0,1}){
   Path a=A,b=B;
   if(sa)std::reverse(a.begin(),a.end());if(sb)std::reverse(b.begin(),b.end());
   for(auto& v:b)v=image[v&255];
   std::array<int,256> bad{};for(int i=trim+1;i<(int)a.size();i++)for(int j=trim+1;j<(int)b.size();j++)bad[a[i]^b[j]]=1;
   for(int t=0;t<256;t++){
    images++;if(bad[t])continue;partial++;
    Path q=b;for(auto &v:q)v=256+(v^t);
    // Each projected coincidence has to be removed from one side, except
    // the two retained ports themselves when they form a vertical edge.
    std::vector<std::pair<int,int>> conflict;
    std::array<int,256> index;index.fill(-1);for(int j=0;j<nb;j++)index[q[j]&255]=j;
    for(int i=0;i<na;i++)if(index[a[i]]>=0)conflict.emplace_back(i,index[a[i]]);
    for(int i=0;i<=trim;i++)for(int j=0;j<=trim;j++){
     bool ok=true;for(auto [x,y]:conflict)if(x>=i&&y>=j&&(x!=i||y!=j)){ok=false;break;}
     if(ok)search(Path(a.begin()+i,a.end()),Path(q.begin()+j,q.end()));
    }
   }
  }
 }while(std::next_permutation(pi.begin(),pi.end()));
 std::cerr<<"coordinate_images "<<images<<" eligible "<<partial<<" attempted "<<attempts<<" nodes "<<nodes<<" capped "<<capped<<"\n";
}
