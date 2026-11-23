// A projected cell may now appear multiple times. Its disjoint induced paths
// must have neither shared vertices nor an edge between visits.
#define main eight_block_entry
#include "search_q9_six_cube_chain.cpp"
#undef main
struct Revisit {
 std::vector<int> cells;std::vector<Family> fam;std::vector<std::array<P,64>> index;
 std::vector<State> chosen;std::vector<int> upper;
 std::vector<std::array<int,64>> suffix;
 std::vector<std::vector<int>> continuation;
 int n,target,best=0,special=-1;long long cap,nodes=0;bool capped=false;
 void dfs(int depth,int size){
  if(nodes>=cap){capped=true;return;}nodes++;
  if(depth==n){
   best=std::max(best,size-1);if(size<target+1)return;
   P path;
   for(int i=0;i<n;i++){
    auto s=chosen[i];auto rem=s.mask;int v=s.s;while(true){
     path.push_back((cells[i]<<6)+v);rem^=B(v);if(!rem)break;
     M opt=rem&nb[v];if(pop(opt)!=1)std::exit(4);v=__builtin_ctzll(opt);
    }
    if(v!=s.t)std::exit(5);
   }
   if((int)path.size()!=size)std::exit(6);
   for(int j=0;j<size;j++)for(int i=0;i<j;i++)if(path[i]==path[j]||((pop(path[i]^path[j])==1)!=(i+1==j)))std::exit(7);
   std::cout<<"FOUND "<<size-1;for(int x:path)std::cout<<" "<<x;std::cout<<std::endl;std::exit(0);
  }
  int cell=cells[depth],port=0;M block=0;
  if(depth){port=chosen[depth-1].t;block=chosen[depth-1].mask^B(port);}
  for(int j=0;j+1<depth;j++){
   int dist=pop(cell^cells[j]);if(dist==1)block|=chosen[j].mask;
   else if(!dist){M m=chosen[j].mask;block|=m;while(m)block|=nb[low(m)];}
  }
  if(depth && (block&B(port)))return;
  auto test=[&](const State& s){
   if(size+s.n+upper[depth+1]<target+1)return true;
   if(size+continuation[depth][&s-fam[depth].states.data()]<target+1)return false;
   if(!(s.mask&block)){chosen[depth]=s;dfs(depth+1,size+s.n);}
   return capped;
  };
  if(depth){for(int k:index[depth][port])if(test(fam[depth].states[k]))break;}
  else{for(auto& s:fam[depth].states)if(test(s))break;}
 }
 void run(int extra,int trim,int target_,long long cap_){
  target=target_;cap=cap_;n=fam.size();index.resize(n);upper.assign(n+1,0);chosen.resize(n);
  for(int i=n-1;i>=0;i--){
   auto &f=fam[i];f.ext=(special<0 || special==i)?extra:0;f.min_size=std::max(1,pop(f.orig)-((special<0 || special==i)?trim:0));
   for(int v=0;v<64;v++)if(f.ext || f.orig&B(v))f.add(v,v,B(v),0,int(!(f.orig&B(v))));
   std::sort(f.states.begin(),f.states.end(),[](const State& a,const State& b){if(a.n!=b.n)return a.n>b.n;if(a.s!=b.s)return a.s<b.s;return a.mask<b.mask;});
   for(int j=0;j<(int)f.states.size();j++)index[i][f.states[j].s].push_back(j);
   if(f.states.empty())return;upper[i]=upper[i+1]+f.states[0].n;
  }
  continuation.resize(n);
  for(int j=n-1;j>=0;j--){
    auto &here=fam[j].states;auto &score=continuation[j];score.resize(here.size());
    for(int k=0;k<(int)here.size();k++){
      auto &z=here[k];int extension=-1000;
      if(j+1==n)extension=0;
      else{
        M block=z.mask^B(z.t);
        for(int h:index[j+1][z.t]){
          if(continuation[j+1][h]<=extension)break;
          if(!(block&fam[j+1].states[h].mask)){extension=continuation[j+1][h];break;}
        }
      }
      score[k]=z.n+extension;
    }
    for(auto &row:index[j])std::sort(row.begin(),row.end(),[&](int a,int b){return score[a]>score[b];});
    // DFS relies on decreasing local lengths; reestablish those after the DP.
  }
  for(int j=0;j<n;j++)for(auto &row:index[j])std::sort(row.begin(),row.end());
  dfs(0,0);std::cerr<<"visits "<<n<<" nodes "<<nodes<<" cap "<<capped<<" upper0 "<<upper[0]<<" best_complete "<<best<<std::endl;
 }
};
int main(int argc,char**argv){
 if(argc!=6 && argc!=7)return 2;
 for(int v=0;v<64;v++)for(int d=0;d<6;d++)nb[v]|=B(v^(1<<d));
 int n,rows=0;while(std::cin>>std::dec>>n && rows++<atoi(argv[5])){
  Revisit s;s.fam.resize(n);for(auto& f:s.fam){int c;std::cin>>std::dec>>c>>std::hex>>f.orig;s.cells.push_back(c);}
  if(argc==6)s.run(atoi(argv[1]),atoi(argv[2]),atoi(argv[3]),atoll(argv[4]));
  else for(int j=0;j<n;j++){Revisit w=s;w.special=j;w.run(atoi(argv[1]),atoi(argv[2]),atoi(argv[3]),atoll(argv[4]));}
 }
}
