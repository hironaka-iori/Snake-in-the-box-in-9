#define main old_join_main
#include "join.cpp"
#undef main
#include <unordered_set>
#include <deque>
struct Grow{
 deque<int> p;int load[512]{},budget,nodes=0,before;vector<int> best;
 void add(int x,int delta){load[x]+=2*delta;for(int d=0;d<9;d++)load[x^1<<d]+=delta;}
 void run(bool left,int rem){nodes++;if((int)p.size()>before){before=p.size();best.assign(p.begin(),p.end());}
  if(!rem)return;if(left)run(false,rem);
  int x=left?p.front():p.back();
  for(int d=0;d<9;d++){int y=x^1<<d;if(load[y]!=1)continue;
   add(y,1);if(left)p.push_front(y);else p.push_back(y);run(left,rem-1);
   if(left)p.pop_front();else p.pop_back();add(y,-1);}
 }
};
int bridge_min,bridge_max,outer,threshold,process_mod,residue,globalbest=0;
long long bridge_calls=0,starts=0,deep=0,unique_deep=0,growth=0;unordered_set<string> known;
string key(const vector<int>& p){string w;for(int i=1;i<(int)p.size();i++)w.push_back('0'+__builtin_ctz(p[i-1]^p[i]));
 auto normal=[](string z){int n=0,perm[9]{};for(char& c:z){int a=c-'0';if(!perm[a])perm[a]=++n;c='0'+perm[a]-1;}return z;};
 auto a=normal(w);reverse(w.begin(),w.end());return min(a,normal(w));}
struct Work{
 vector<int> left,right;int tag,len;int covered[512]{},assignment[9]{};
 void mark(int v,int change){covered[v]+=2*change;for(int j=0;j<9;j++)covered[v^1<<j]+=change;}
 void candidate(int rt,int depth){
  deep++;vector<int> total=left;total.insert(total.end(),right.begin(),right.end());if(!known.insert(key(total)).second)return;unique_deep++;
  Grow g;g.p.assign(total.begin(),total.end());for(int x:total)g.add(x,1);g.before=globalbest+1;g.run(true,outer);growth+=g.nodes;
  if(!g.best.empty()){globalbest=g.best.size()-1;cout<<"W "<<globalbest<<" "<<tag<<" "<<rt<<" "<<len<<" "<<depth<<" "<<total.size()-1<<" "<<g.nodes;
   for(int v:g.best)cout<<" "<<v;cout<<endl;}
 }
 void dfs(int node,int x,int k,int avail,int depth){calls++;
  if(depth&&int(left.size())-1+depth>=threshold)candidate(trie[node].any,depth);
  for(int d=0;d<=k&&d<9;d++)if(int h=trie[node].ch[d]){
   if(d<k){int v=x^assignment[d];if(covered[v])continue;right.push_back(v);dfs(h,v,k,avail,depth+1);right.pop_back();}
   else for(int bits=avail;bits;bits&=bits-1){int a=bits&-bits,v=x^a;if(covered[v])continue;assignment[d]=a;right.push_back(v);dfs(h,v,k+1,avail^a,depth+1);right.pop_back();}
  }
 }
 void build(int t){
  bridge_calls++;int x=left.back();
  if(t>=bridge_min){
   // All existing vertices except the shared tip block their full closed neighborhoods.
   mark(x,-1);covered[x]+=2;starts++;len=t;dfs(0,x,0,511,0);covered[x]-=2;mark(x,1);
  }
  if(t==bridge_max)return;
  for(int d=0;d<9;d++){int v=x^1<<d;if(covered[v]!=1)continue;left.push_back(v);mark(v,1);build(t+1);mark(v,-1);left.pop_back();}
 }
 void start(int lt){tag=lt;auto w=oriented(lt);left={0};for(char c:w)left.push_back(left.back()^1<<(c-'0'));
  for(int x:left)mark(x,1);build(0);
 }
};
int main(int argc,char**argv){
 bridge_min=atoi(argv[1]);bridge_max=atoi(argv[2]);outer=atoi(argv[3]);threshold=atoi(argv[4]);process_mod=atoi(argv[5]);residue=atoi(argv[6]);int leftkind=atoi(argv[7]);Shape s;
 while(cin>>s.w>>s.id>>s.u>>s.v>>s.orig)shapes.push_back(s);
 for(int i=0;i<2*(int)shapes.size();i++)add(i);
 int cnt=0;for(int i=residue;i<(int)shapes.size();i+=process_mod){if(leftkind&&shapes[i].orig)continue;cnt++;
  for(int a=0;a<2;a++){Work m;m.start(2*i+a);}}
 cout<<"DONE "<<cnt<<" "<<starts<<" "<<calls<<" "<<deep<<" "<<unique_deep<<" "<<growth<<" "<<globalbest<<endl;
}
