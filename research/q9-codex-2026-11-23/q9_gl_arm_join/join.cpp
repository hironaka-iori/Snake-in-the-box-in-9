#include <algorithm>
#include <array>
#include <iostream>
#include <cstdlib>
#include <string>
#include <fstream>
#include <set>
#include <vector>
using namespace std;
struct Shape{string w;int id,u,v,orig;};
struct Node{int ch[9]{},any=-1,modified=-1,fresh=-1;};
vector<Shape> shapes;vector<Node> trie(1);int dims=9;
string oriented(int tag){string w=shapes[tag/2].w;if(tag%2)reverse(w.begin(),w.end());int colors[9]={},n=0;
 for(char& c:w){int d=c-'0';if(!colors[d])colors[d]=++n;c='0'+colors[d]-1;}return w;}
void add(int tag){int at=0;auto w=oriented(tag);for(char c:w){
 int d=c-'0';if(!trie[at].ch[d]){int m=trie.size();trie[at].ch[d]=m;trie.emplace_back();}at=trie[at].ch[d];
 auto& t=trie[at];t.any=tag;if(shapes[tag/2].u)t.modified=tag;if(!shapes[tag/2].orig)t.fresh=tag;
}}
long long calls=0,candidates=0,roots=0;int best[4]{0},goal=192,min_report=180;
struct Search{
 int lt,mode,bridge,axis[9]{};bool blocked[512]{};vector<int> left,right;
 void record(int dep,int rt,int cls){
  if(rt<0)return;int edges=left.size()-1+mode+dep;if(edges<=best[cls])return;best[cls]=edges;
  cout<<"W "<<cls<<" "<<edges<<" "<<lt<<" "<<rt<<" "<<mode<<" "<<dep<<" "<<bridge;
  for(int i=0;i<dims;i++)cout<<" "<<axis[i];for(int x:left)cout<<" "<<x;
  if(mode)cout<<" "<<bridge;for(int y:right)cout<<" "<<y;cout<<endl;
 }
 void dfs(int node,int v,int n,int free,int dep){calls++;
  if(dep&&dep+(int)left.size()-1+mode>=min_report){
   auto &t=trie[node];record(dep,t.any,0);if(shapes[lt/2].u)record(dep,t.modified,1);
   if(!shapes[lt/2].orig)record(dep,t.fresh,2);
   if(!shapes[lt/2].orig)record(dep,t.any,3);else record(dep,t.fresh,3);
  }
  for(int d=0;d<=n&&d<dims;d++)if(int k=trie[node].ch[d]){
   if(d<n){int x=v^axis[d];candidates++;if(blocked[x])continue;right.push_back(x);dfs(k,x,n,free,dep+1);right.pop_back();}
   else for(int b=free;b;b&=b-1){int u=b&-b,x=v^u;candidates++;if(blocked[x])continue;
    axis[d]=u;right.push_back(x);dfs(k,x,n+1,free^u,dep+1);right.pop_back();axis[d]=0;}
  }
 }
 void run(int tag){
  lt=tag;auto w=oriented(lt);left={0};for(char c:w)left.push_back(left.back()^1<<(c-'0'));
  int seam=left.back();for(int&v:left)v^=seam;
  fill(blocked,blocked+512,false);
  for(int i=0;i+1<(int)left.size();i++){int v=left[i];blocked[v]=true;for(int j=0;j<dims;j++)blocked[v^1<<j]=true;}blocked[0]=true;
  mode=0;bridge=0;roots++;dfs(0,0,0,(1<<dims)-1,0);
  vector<int> tips;for(int j=0;j<dims;j++)if(!blocked[1<<j])tips.push_back(1<<j);
  mode=1;for(int j=0;j<dims;j++)blocked[1<<j]=true;
  for(int h:tips){bridge=h;roots++;dfs(0,h,0,(1<<dims)-1,0);}
 }
};
int main(int argc,char**argv){
 if(getenv("Q9_GL_MIN"))min_report=atoi(getenv("Q9_GL_MIN"));int a=atoi(argv[1]),b=atoi(argv[2]);if(argc>=4)dims=atoi(argv[3]);Shape s;
 while(cin>>s.w>>s.id>>s.u>>s.v>>s.orig)shapes.push_back(s);
 set<string> previous;int lf=-1,rf=-1;
 if(argc>=7){ifstream in(argv[4]);Shape x;while(in>>x.w>>x.id>>x.u>>x.v>>x.orig)previous.insert(x.w);lf=atoi(argv[5]);rf=atoi(argv[6]);}
 for(int i=0;i<2*(int)shapes.size();i++)if(rf<0||int(!previous.count(shapes[i/2].w))==rf)add(i);cout<<"BANK "<<shapes.size()<<" "<<trie.size()<<endl;
 for(int i=a;i<min((int)shapes.size(),b);i++){if(lf>=0&&int(!previous.count(shapes[i].w))!=lf)continue;Search work;work.run(2*i);work.run(2*i+1);
  if((i-a+1)%500==0)cout<<"AT "<<i+1<<" "<<calls<<endl;}
 cout<<"DONE "<<a<<" "<<min((int)shapes.size(),b)<<" "<<roots<<" "<<calls<<" "<<candidates;for(int b:best)cout<<" "<<b;cout<<endl;
}
