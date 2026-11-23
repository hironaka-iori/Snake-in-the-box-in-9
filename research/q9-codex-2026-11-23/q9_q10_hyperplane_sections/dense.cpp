#define SWEEP_ONLY
#include "sweep.cpp"
#undef main
#include <random>
// Split the possible deletion vertices into blocks. Every realization for its
// block must admit all basis directions on the compulsory intersection.
struct Dense: Sweep{
 vector<int> all;vector<pair<int,int>> deletions;int d;uint64_t fits=0;
 Dense(vector<int> core,vector<int> input,vector<pair<int,int>> rm,vector<int> ts,int holes):
   Sweep(core,ts),all(input),deletions(rm),d(holes){}
 bool finish(int edges) override{
  array<int,512> coord;coord.fill(-1);coord[0]=0;vector<int> space{0};
  for(int i=0;i<9;i++){int g=bs[i];if(coord[g]>=0)return false;int len=space.size();for(int k=0;k<len;k++){int y=space[k]^g;coord[y]=coord[space[k]]^(1<<i);space.push_back(y);}}
  ranked++;Bits full;for(int x:all)full.set(coord[x]);array<int,512> degree{};int original_edges=0;vector<int> bad;
  for(int x:all){int v=coord[x];for(int k=0;k<9;k++)degree[v]+=full[v^(1<<k)];original_edges+=degree[v];if(degree[v]>2)bad.push_back(v);}original_edges/=2;
  for(auto [u,v]:deletions){
   int a=coord[u],b=v<0?-1:coord[v];bool ok=true;
   for(int t:bad)if(t!=a&&t!=b&&degree[t]-((t^a)!=0&&has_single_bit((unsigned)(t^a)))-(b>=0&&has_single_bit((unsigned)(t^b)))>2){ok=false;break;}
   if(!ok)continue;int kept=all.size()-d;
   int e=original_edges-degree[a]-(b<0?0:degree[b]-has_single_bit((unsigned)(a^b)));
   if(e>kept-1)continue;Bits fixed=full;fixed.reset(a);if(b>=0)fixed.reset(b);
   fits++;
   for(int j=0;j<goals.size();j++){int t=goals[j],h=t+1-kept;if(h<0||e<kept-1-h)continue;tried[j]++;
    unordered_set<Bits> dead;vector<int> path;if(grow_focus(fixed,h,path,dead)){success=t;answer=path;
      cout<<"FOUND TARGET "<<t<<" REMOVED "<<u<<" "<<v<<" BASIS";for(int x:bs)cout<<" "<<x;cout<<" PATH";for(int x:path)cout<<" "<<x;cout<<endl;return true;}
   }
  }return false;
 }
};
int main(int argc,char**argv){if(argc!=4&&argc!=5)return 2;int d=atoi(argv[1]),block=atoi(argv[2]),cap=atoi(argv[3]),caseid=0;string line;mt19937 rng(517692);
 while(getline(cin,line)){istringstream ss(line);int r,m,b,n,x;ss>>r>>m>>b>>n;vector<int> p;while(ss>>x)p.push_back(x);
  vector<int> q=argc==5?vector<int>{atoi(argv[4])}:vector<int>{192,195,196};vector<int> ts;for(int t:q)if(n-d<=t+1&&n-d>=180)ts.push_back(t);if(ts.empty()||(argc==4&&(n>197+d||n<193+d)))continue;
  if(caseid>=cap)break;caseid++;vector<int> random=p;shuffle(random.begin(),random.end(),rng);
  uint64_t nodes=0,ranked=0,fits=0,groups=0,rmcount=0;array<uint64_t,3> tries{};
  for(int i=0;i<n;i+=block)for(int j=(d==1?i:0);j<=i;j+=block){
   vector<pair<int,int>> rm;Bits apart;
   for(int k=i;k<min(i+block,n);k++)apart.set(random[k]);
   for(int k=j;k<min(j+block,n);k++)apart.set(random[k]);
   for(int k=i;k<min(i+block,n);k++){if(d==1)rm.emplace_back(random[k],-1);else for(int l=j;l<min(j+block,n);l++)if(j!=i||l<k)rm.emplace_back(random[k],random[l]);}
   if(rm.empty())continue;vector<int> core;for(int y:p)if(!apart[y])core.push_back(y);Dense s(core,p,rm,ts,d);vector<int> opts(511);iota(opts.begin(),opts.end(),1);sort(opts.begin(),opts.end(),[&](int a,int b){return pair(s.weight[a],a)<pair(s.weight[b],b);});
   if(s.dfs(opts,Bits{},Bits{},0)){cout<<"SOURCE "<<r<<" "<<m<<" "<<b<<endl;return 0;}
   nodes+=s.nodes;ranked+=s.ranked;fits+=s.fits;groups++;rmcount+=rm.size();for(int k=0;k<ts.size();k++)tries[k]+=s.tried[k];
  }
  cout<<r<<" "<<m<<" "<<b<<" "<<n<<" CLOSED "<<d<<" "<<rmcount<<" "<<groups<<" "<<nodes<<" "<<ranked<<" "<<fits;for(int k=0;k<ts.size();k++)cout<<" "<<ts[k]<<"="<<tries[k];cout<<endl;
 }
}
