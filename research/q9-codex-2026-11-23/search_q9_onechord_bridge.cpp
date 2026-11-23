// Exact within one chosen interval if its node budget is not exhausted.
#define main fixed_walk_original_main
#include "search_q9_fixed_walk.cpp"
#undef main
#include <deque>
#include <functional>
#include <fstream>
#include <unordered_set>
#include <numeric>
#include <set>
#include <chrono>

struct Repair {
 Walk w;
 int k,l,r,cap,nodes=0;
 bool capped=false;
 vector<int> prefix,suffix,result;
 mt19937 rng;
 Repair(const vector<int>&path,int left,int right,int budget,int seed):
  w(9,path),k(right-left+1),l(left),r(right),cap(budget),rng(seed){}
 void neighbors(int x,int other,int n,vector<int>&out){
  for(int d=0;d<9;d++){
   int v=x^(1<<d);if(w.cnt[v])continue;
   if(other<0){if(w.near[v]!=1)continue;}
   else{
    int h=popcount((unsigned)(v^other));
    if(h>n|| (n==1&&h!=1))continue;
    if(w.near[v]!=(1+(n==1)))continue;
   }
   out.push_back(v);
  }
 }
 bool dfs(int a,int b,int n){
  if(++nodes>cap){capped=true;return false;}
  if(n==0){
   result.assign(w.p.begin(),w.p.begin()+l);
   result.insert(result.end(),prefix.begin(),prefix.end());result.insert(result.end(),suffix.rbegin(),suffix.rend());
   result.insert(result.end(),w.p.begin()+r+1,w.p.end());
   Walk test(9,result);test.verify();if(test.E)abort();return true;
  }
  vector<int>A,B;neighbors(a,b,n,A);if(A.empty())return false;
  bool rev=false;
  if(b>=0){
   neighbors(b,a,n,B);
   if(B.empty())return false;
   rev=B.size()<A.size()||(A.size()==B.size()&&n%2==0);
  }
  auto &next=rev?B:A;
  shuffle(next.begin(),next.end(),rng);
  if(n>=5&&n%5==0){
   // An induced completion may use open cells and either legal frontier.
   array<bool,512> allowed{},seen{};array<int,512> queue;int count[2]{},head=0,tail=0;
   for(int v=0;v<512;v++)allowed[v]=!w.cnt[v]&&!w.near[v];
   for(int v:A)allowed[v]=true;for(int v:B)allowed[v]=true;
   for(int v:A)if(!seen[v]){seen[v]=1;queue[tail++]=v;}
   while(head<tail){
    int v=queue[head++];count[popcount((unsigned)v)%2]++;
    for(int d=0;d<9;d++){int u=v^(1<<d);if(allowed[u]&&!seen[u]){seen[u]=1;queue[tail++]=u;}}
   }
   if(b>=0&&n>=15){
    // In the block-cut tree only biconnected blocks lying on the a--b route
    // can occur in any simple bridge. Peel all other branches before counting.
    if(none_of(B.begin(),B.end(),[&](int v){return seen[v];}))return false;
    allowed[a]=allowed[b]=true;
    array<int,512> disc{},low{};int timer=0;vector<pair<int,int>> stack;
    vector<vector<int>> blocks;
    function<void(int,int)> visit=[&](int v,int parent){
     disc[v]=low[v]=++timer;
     for(int d=0;d<9;d++){
      int u=v^(1<<d);if(!allowed[u]||u==parent)continue;
      if(!disc[u]){
       stack.emplace_back(v,u);visit(u,v);low[v]=min(low[v],low[u]);
       if(low[u]>=disc[v]){
        vector<int> block;
        while(true){auto e=stack.back();stack.pop_back();block.push_back(e.first);block.push_back(e.second);if(e==pair{v,u})break;}
        sort(block.begin(),block.end());block.erase(unique(block.begin(),block.end()),block.end());blocks.push_back(move(block));
       }
      }else if(disc[u]<disc[v]){stack.emplace_back(v,u);low[v]=min(low[v],disc[u]);}
     }
    };
    visit(a,-1);if(!disc[b])return false;
    vector<vector<int>> tree(512+blocks.size());for(int i=0;i<(int)blocks.size();i++)for(int u:blocks[i]){tree[512+i].push_back(u);tree[u].push_back(512+i);}
    vector<int>pred(tree.size(),-2),front{a};pred[a]=-1;
    for(size_t h=0;h<front.size()&&pred[b]==-2;h++)for(int u:tree[front[h]])if(pred[u]==-2){pred[u]=front[h];front.push_back(u);}
    if(pred[b]==-2)return false;
    // Along the block-cut route the two entry/exit cut vertices are mandatory.
    // Count parity separately within each block, then add edge capacities.
    int edges_upper=0;
    for(int u=b;u!=a;){
     int block_node=pred[u],v=pred[block_node];auto &block=blocks[block_node-512];
     int bins[2]{};for(int x:block)bins[popcount((unsigned)x)%2]++;
     int color=popcount((unsigned)u)%2;
     int upper=(popcount((unsigned)(u^v))%2)?
      2*min(bins[0],bins[1])-1:2*min(bins[color]-1,bins[1-color]);
     if(block.size()>2&&block.size()<=14){
      array<short,512> inside{};for(int x:block)inside[x]=1;
      array<short,512> near{};for(int d=0;d<9;d++)near[u^(1<<d)]++;
      inside[u]=0;int opt=0;
      function<void(int,int)> small=[&](int x,int len){
       if(x==v){opt=max(opt,len);return;}
       for(int d=0;d<9;d++){int y=x^(1<<d);if(!inside[y]||near[y]!=1)continue;
        inside[y]=0;for(int z=0;z<9;z++)near[y^(1<<z)]++;
        small(y,len+1);for(int z=0;z<9;z++)near[y^(1<<z)]--;inside[y]=1;
       }
      };
      small(u,0);upper=min(upper,opt);
     }
     edges_upper+=upper;u=v;
    }
    if(edges_upper<n+1)return false;
    array<bool,512>route{};
    for(int u=b;u!=-1;u=pred[u])if(u>=512)for(int x:blocks[u-512])route[x]=true;
    count[0]=count[1]=0;
    for(int v=0;v<512;v++)if(route[v]&&v!=a&&v!=b)count[popcount((unsigned)v)%2]++;
   }
   int first=1-popcount((unsigned)a)%2;
   if(count[first]<(n+1)/2||count[1-first]<n/2)return false;
   if(b>=0&&none_of(B.begin(),B.end(),[&](int v){return seen[v];}))return false;
  }
  auto &track=rev?suffix:prefix;
  for(int v:next){
   w.edit(v,1);track.push_back(v);
   if(dfs(rev?a:v,rev?v:b,n-1))return true;
   track.pop_back();w.edit(v,-1);
   if(capped)break;
  }
  return false;
 }
 bool run(){
  for(int i=l;i<=r;i++)w.edit(w.p[i],-1);
  int b=r+1==(int)w.p.size()?-1:w.p[r+1];
  if(w.E+k+(b>=0)>0)return false;
  return dfs(w.p[l-1],b,k);
 }
};
// Exact isometry key for the two fixed, ordered pieces. Prefix length and
// bridge displacement identify the endpoints; independent axis names are immaterial.
string domain_key(vector<int> p,int start,int size){
 auto orientation=[&](){
  array<int,9> label;label.fill(-1);int next=0;
  string code;code.push_back(char(start));code.push_back(char(p.size()-start-size));
  for(int t=1;t<(int)p.size();t++){
   if(t>=start&&t<=start+size)continue;
   int d=countr_zero((unsigned)(p[t]^p[t-1]));
   if(label[d]<0)label[d]=next++;
   code.push_back(char(label[d]));
  }
  int gap=(start>0&&start+size<(int)p.size())?(p[start-1]^p[start+size]):0;
  int mask=0,unseen=0;
  for(int d=0;d<9;d++)if(gap&(1<<d)){if(label[d]>=0)mask|=1<<label[d];else ++unseen;}
  code.push_back(char(mask&255));code.push_back(char(mask>>8));code.push_back(char(unseen));
  return code;
 };
 auto key=orientation();reverse(p.begin(),p.end());start=p.size()-start-size;
 return min(key,orientation());
}
int main(int argc,char **argv){
 if(argc!=4&&argc!=5)return 2;
 int span=stoi(argv[1]),cap=stoi(argv[2]),seed=stoi(argv[3]);
 string line;long long total=0,proven=0,unknown=0,reused=0;int row=0;
 unordered_set<string> excluded;
 set<pair<int,int>> selected;
 if(argc==5){ifstream input(argv[4]);if(!input)return 5;string ln;while(getline(input,ln)){istringstream rec(ln);string tag;int u,v;if(rec>>tag>>u>>v&&tag=="CAP")selected.emplace(u,v);}}
 while(getline(cin,line)){
  istringstream in(line);vector<int>path;int x;while(in>>x)path.push_back(x);if(path.empty())continue;
  Walk input(9,path);input.verify();if(input.E!=1)return 3;
  int L=path.size()-1,i=-1,j=-1;
  for(int u=0;u<=L;u++)for(int t=u+2;t<=L;t++)if(popcount((unsigned)(path[u]^path[t]))==1){i=u;j=t;}
  set<int>windows;
  for(int endpoint:{i,j})for(int start=max(0,endpoint-span+1);start<=min(endpoint,L-span+1);start++)windows.insert(start);
  for(int start:windows){
   if(argc==5&&!selected.count(pair{row,start}))continue;
   string id=domain_key(path,start,span);
   if(excluded.count(id)){proven++;reused++;continue;}
   vector<int>p=path;int s=start;
   if(s==0){reverse(p.begin(),p.end());s=L-span+1;}
   Repair rep(p,s,s+span-1,cap,seed+row*1000+start);
   if(rep.run()){
    cout<<"FOUND "<<row<<" "<<start;for(int v:rep.result)cout<<" "<<v;cout<<endl;return 0;
   }
   total+=rep.nodes;unknown+=rep.capped;proven+=!rep.capped;
   if(!rep.capped)excluded.insert(move(id));else cout<<"CAP "<<row<<" "<<start<<" "<<rep.nodes<<"\n";
  }
  if(++row%25==0)cout<<"CHECK "<<row<<" excluded "<<proven<<" cap "<<unknown<<" nodes "<<total<<endl;
 }
 cout<<"DONE "<<row<<" excluded "<<proven<<" cap "<<unknown<<" nodes "<<total<<" reused "<<reused<<endl;
}
