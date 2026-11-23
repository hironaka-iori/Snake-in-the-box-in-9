#define NO_CATALOGUE_MAIN
#include "catalogue.cpp"
struct FreeTail:Matcher {
 long long clean=0,bridges=0,bridgeNodes=0,bridgeLimits=0,growNodes=0,growLimits=0;int bound=1800,localBridge=0,localGrow=0;
 void more(){
   if(search.hit||localGrow>=800)return;
   ++localGrow;++growNodes;auto& z=search;z.save(z.seed,z.tail);int u=z.tail.back();
   for(int k=0;k<8;k++){int x=u^1<<k;if(!z.can(x))continue;z.tail.push_back(x);z.mark(x,1);more();z.mark(x,-1);z.tail.pop_back();if(z.hit||localGrow>=800)break;}
 }
 void dfs(int room){
   if(search.hit||localBridge>=bound)return;
   ++localBridge;++bridgeNodes;auto& z=search;int u=z.seed.back();
   if(dist(u,z.y)==1){
     if(!z.occ[z.y]&&z.adj[z.y]==1){z.mark(z.y,1);z.seed.push_back(z.y);++bridges;localGrow=0;more();growLimits+=localGrow>=800;z.seed.pop_back();z.mark(z.y,-1);}return;
   }
   if(room<dist(u,z.y))return;
   for(int k=0;k<8;k++){int x=u^1<<k;if(!z.can(x))continue;z.mark(x,1);z.seed.push_back(x);dfs(room-1);z.seed.pop_back();z.mark(x,-1);if(z.hit||localBridge>=bound)break;}
 }
 void run(P p,int a,int b,int stride,int row){
   auto& z=search;z.id=row;z.best2=z.best3=0;z.ans2.clear();z.ans3.clear();array<int,8> perm;iota(perm.begin(),perm.end(),0);int j=0;
   do{if(j++%stride)continue;++perms;int f[256]{},inv[256]{};
     for(int v=1;v<256;v++){f[v]=f[v&(v-1)]^(1<<perm[countr_zero(unsigned(v))]);inv[f[v]]=v;}
     for(int i=0;i<2;i++){z.low=p;if(i)reverse(z.low.begin(),z.low.end());z.s=z.low.front();z.e=z.low.back();
       Mask forbid{};fill(z.blocked,z.blocked+256,0);for(int v:p){z.blocked[v]=1;if(v!=z.e){int x=f[v^z.e];forbid[x/64]|=1ull<<(x%64);}}
       z.blocked[a]=z.blocked[b]=1;for(int v:{a,b}){int x=f[v^z.e];forbid[x/64]|=1ull<<(x%64);}
       for(auto& g:groups){compared+=g.size();for(auto& arm:g){if((arm.m[0]&forbid[0])|(arm.m[1]&forbid[1])|(arm.m[2]&forbid[2])|(arm.m[3]&forbid[3]))continue;
         ++clean;z.tail.clear();for(int v:arm.p){int x=inv[v]^z.e;z.tail.push_back(x);z.mark(x,1);}
         if(z.adj[z.s]==0){
           z.seed={z.s};z.mark(z.s,1);
           for(int side=0;side<2;side++){z.y=side?b:a;z.z=side?a:b;if(z.adj[z.y]==0){localBridge=0;dfs(20);bridgeLimits+=localBridge>=bound;}}
           z.mark(z.s,-1);
         }
         for(int x:z.tail)z.mark(x,-1);if(z.hit)break;
       }if(z.hit)break;}
       if(z.hit)break;
     }if(z.hit)break;
   }while(next_permutation(perm.begin(),perm.end()));
   if(!z.ans3.empty()){auto&v=z.ans3;z.out<<row<<' '<<v.size()-1;for(int x:v)z.out<<' '<<x;z.out<<endl;}
 }
};
int main(int argc,char**argv){if(argc!=8)return 2;FreeTail z;z.search.out.open(argv[3]);z.load(argv[1],stoi(argv[4]),true);int stride=stoi(argv[5]),lo=stoi(argv[6]),hi=stoi(argv[7]);ifstream in(argv[2]);string w;int a,b;
 for(int i=0;in>>w>>a>>b;i++){if(i<lo||i>=hi)continue;P p{0};for(char k:w)p.push_back(p.back()^(1<<(k-'0')));z.run(p,a,b,stride,i);if(z.search.hit)break;}
 cout<<"permutations "<<z.perms<<" masks "<<z.compared<<" valid_tails "<<z.clean<<" bridges "<<z.bridges<<" bridge_nodes "<<z.bridgeNodes<<" capped_bridge_searches "<<z.bridgeLimits<<" extension_nodes "<<z.growNodes<<" capped_extensions "<<z.growLimits<<" found192 "<<z.search.hit<<endl;
}
