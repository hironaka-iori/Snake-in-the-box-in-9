// Exact two-colour lift of a prescribed simple walk in Q8. Vertices between
// nonconsecutive contacts form runs where a maximum independent set supplies
// the vertical switches, with one switch lost if the prescribed parity differs.
#include <algorithm>
#include <array>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <vector>
using Path=std::vector<int>;
struct DSU{
 int par[260],flip[260]{};
 DSU(){for(int i=0;i<260;++i)par[i]=i;}
 int root(int a){if(par[a]==a)return a;int b=par[a];par[a]=root(b);flip[a]^=flip[b];return par[a];}
 bool link(int a,int b,int dx){int x=root(a),y=root(b);int diff=flip[a]^flip[b]^dx;if(x==y)return diff==0;par[x]=y;flip[x]=diff;return true;}
};
bool valid(const Path &p,int dim){
 for(int j=0;j<(int)p.size();++j){if(p[j]<0||p[j]>=(1<<dim))return false;
 for(int i=0;i<j;++i){int d=__builtin_popcount((unsigned)(p[i]^p[j]));if(d==0||(d==1)!=(j==i+1))return false;}}return true;
}
struct Lift{
 Path p,forced;DSU dsu;int m,base=0;
 std::array<int,256> idx,group,assigned;std::vector<std::array<int,3>> terms;
 std::vector<int> order;
 Lift(const Path &walk):p(walk),m(walk.size()){idx.fill(-1);group.fill(-1);assigned.fill(-1);}
 bool prepare(){
  bool hit[256]{};
  for(int i=0;i<m;++i){if(idx[p[i]]!=-1 || (i&&__builtin_popcount((unsigned)(p[i]^p[i-1]))!=1))return false;idx[p[i]]=i;}
  for(int i=0;i<m;++i)for(int k=0;k<8;++k){int j=idx[p[i]^(1<<k)];
   if(j<=i+1)continue;
   hit[i]=hit[j]=true;if(!dsu.link(i,j,1))return false;
  }
  for(int i=0;i<m;++i)if(hit[i]){if(i&&hit[i-1]&&!dsu.link(i-1,i,0))return false;forced.push_back(i);}
  base=m-1;if(forced.empty()){base+=(m+1)/2;return true;}
  base+=(forced.front()+1)/2+(m-forced.back())/2;
  std::array<int,256> weight{};
  for(int i:forced){int root=dsu.root(i);if(group[root]<0){group[root]=order.size();order.push_back(group[root]);}}
  for(int j=1;j<(int)forced.size();++j){int a=forced[j-1],b=forced[j],k=(b-a)/2;
   int x=group[dsu.root(a)],y=group[dsu.root(b)],desired=(k%2)^dsu.flip[a]^dsu.flip[b];
   base+=k;
   if(x==y)base-=desired;else {terms.push_back({x,y,desired});++weight[x];++weight[y];}
  }
  std::sort(order.begin(),order.end(),[&](int a,int b){return weight[a]>weight[b];});return true;
 }
 bool search(int j,int slack){
  if(slack<0)return false;if(j==(int)order.size())return true;
  int x=order[j];for(int b=0;b<(j?2:1);++b){assigned[x]=b;int loss=0;
   for(auto [a,c,v]:terms){if((a==x||c==x)&&assigned[a]>=0&&assigned[c]>=0)loss+=((assigned[a]^assigned[c])!=v);}
   if(search(j+1,slack-loss))return true;
  }assigned[x]=-1;return false;
 }
 Path build(){
  std::vector<bool> sw(m);
  auto fill=[&](int start,int count){for(int i=0;i<count;i++)sw[start+2*i]=true;};
  int color=0;
  if(forced.empty())fill(0,(m+1)/2);
  else{
   auto col=[&](int i){return assigned[group[dsu.root(i)]]^dsu.flip[i];};
   int left=(forced.front()+1)/2;color=col(forced.front())^(left%2);fill(0,left);
   for(int j=1;j<(int)forced.size();++j){int a=forced[j-1],b=forced[j],k=(b-a)/2;
    k-=((k%2)!=(col(a)^col(b)));if(k<0)std::abort();fill(a+1,k);}
   fill(forced.back()+1,(m-forced.back())/2);
  }
  Path out;for(int i=0;i<m;++i){out.push_back(p[i]+256*color);if(sw[i]){color^=1;out.push_back(p[i]+256*color);}}return out;
 }
};
Path project(const Path &p,int axis){
 Path out;int low=(1<<axis)-1;for(int x:p){int v=(x&low)|((x>>(axis+1))<<axis);if(out.empty()||out.back()!=v)out.push_back(v);}return out;
}
bool mutate(Path &p,std::mt19937 &rng){
 int n=p.size();std::array<int,256> pos;pos.fill(-1);for(int i=0;i<n;++i)pos[p[i]]=i;
 int i=rng()%(n-1),d=1<<(rng()%8),op=rng()%6;
 if(op==0){int u=p[i]^d,v=p[i+1]^d;if(pos[u]>=0||pos[v]>=0)return false;p.insert(p.begin()+i+1,{u,v});}
 else if(op==1){if(i+3>=n||__builtin_popcount((unsigned)(p[i]^p[i+3]))!=1)return false;p.erase(p.begin()+i+1,p.begin()+i+3);}
 else if(op==2){if(i+2>=n)return false;int v=p[i]^p[i+1]^p[i+2];if(pos[v]>=0)return false;p[i+1]=v;}
 else{bool flipped=rng()%2;if(flipped)std::reverse(p.begin(),p.end());int v=p.back()^d;
  if(flipped && pos[v]>=0)pos[v]=n-1-pos[v];
  if(op==3){if(pos[v]>=0)return false;p.push_back(v);}
  if(op==4){if(pos[v]<0||pos[v]>=n-2)return false;std::reverse(p.begin()+pos[v]+1,p.end());}
  if(op==5){if(n<50)return false;p.pop_back();}
 }return true;
}
int main(int argc,char**argv){
 if(argc<4||argc>5)return 2;bool near=argc==5;int target=std::stoi(argv[1]),trials=std::stoi(argv[2]);std::mt19937 rng(std::stoul(argv[3]));
 std::string row;std::vector<Path> bank;std::set<Path> known;long long feasible=0,checked=0;int best=0;
 auto test=[&](const Path &q,int threshold){
  Lift l(q);++checked;if(!l.prepare())return -1;++feasible;
  for(int score=l.base;score>=threshold;--score){if(!l.search(0,l.base-score))continue;
   Path out=l.build();if((int)out.size()!=score+1||!valid(out,9))std::abort();best=std::max(best,score);
   if(score>=target){std::cout<<"FOUND";for(int v:out)std::cout<<" "<<v;std::cout<<std::endl;std::exit(0);}return score;
  }return -1;
 };
 while(std::getline(std::cin,row)){Path p;std::istringstream in(row);int x;while(in>>x)p.push_back(x);if(p.size()<3||p.size()>512)return 3;
  if(!near&&!valid(p,9))return 3;
  for(int i=0;i<(int)p.size();++i)if(p[i]<0||p[i]>=512||(i&&__builtin_popcount((unsigned)(p[i]^p[i-1]))!=1))return 3;
  for(int axis=0;axis<9;++axis){auto q=project(p,axis);if(known.insert(q).second){int score=test(q,near?target-8:int(p.size())-1);
    if(score<0&&!near)return 4;if(score>=0)bank.push_back(q);}}}
 if(bank.empty())return 2;size_t initial=bank.size();
 for(int it=0;it<trials;++it){auto q=bank[rng()%bank.size()];int n=1+rng()%5,ok=0;
  for(int k=0;k<n*8&&ok<n;++k)ok+=mutate(q,rng);if(!ok)continue;
  int merit=test(q,target-6);if(merit>=target-4&&bank.size()<initial+20000&&known.insert(q).second)bank.push_back(q);
 }
 std::cout<<"DONE initial "<<initial<<" trials "<<trials<<" tested "<<checked<<" consistent "<<feasible<<" bank "<<bank.size()<<" best "<<best<<std::endl;
 return 0;
}
