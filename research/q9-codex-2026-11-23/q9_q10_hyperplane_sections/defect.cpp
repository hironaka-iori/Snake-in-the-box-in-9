// Exact single-deletion search. Before the first degree-three event the deletion
// is unspecified. At that event its possible positions shrink to at most four.
#define SWEEP_ONLY
#include "sweep.cpp"
#include <memory>
struct Small {array<unsigned long long,8> z{};};
struct OneDrop{
 vector<int> p,ts,bs;vector<unique_ptr<Sweep>> cache;array<int,512> wt{};array<Small,512> hit{};Bits membership;
 uint64_t nodes=0,fixnodes=0,fixcalls=0;int N,mh=0;
 OneDrop(vector<int>v,vector<int>t):p(v),ts(t),cache(512),N(p.size()){for(int x:p)membership.set(x);for(int g=1;g<512;g++){for(int x:p)if(membership[x^g]){hit[g].z[x/64]|=1ULL<<(x%64);wt[g]++;}wt[g]/=2;}for(int t:ts)mh=max(mh,t+2-N);}
 Sweep& solver(int x){if(!cache[x]){vector<int>c;for(int v:p)if(v!=x)c.push_back(v);cache[x]=make_unique<Sweep>(c,ts);}return *cache[x];}
 bool fixed(int x,const vector<int>&opts,int first){
   Sweep&s=solver(x);Bits one,two;int edges=0;for(int g:bs){if((two&s.support[g]).any())return false;two|=one&s.support[g];one^=s.support[g];edges+=s.weight[g];}
   if(edges>N-2)return false;int need=9-bs.size();bool yes=false;s.bs=bs;fixcalls++;auto prev=s.nodes;
   if(!need){if(edges>=N-2-mh)yes=s.finish(edges);}else{
   vector<int> candidates;for(int j=first;j<opts.size();j++){int g=opts[j];if((two&s.support[g]).none())candidates.push_back(g);}
   sort(candidates.begin(),candidates.end(),[&](int a,int b){return pair(s.weight[a],a)<pair(s.weight[b],b);});yes=s.dfs(candidates,one,two,edges);}
   fixnodes+=s.nodes-prev;if(yes){cout<<"FOUND TARGET "<<s.success<<" REMOVED "<<x<<" BASIS";for(int g:s.bs)cout<<" "<<g;cout<<" PATH";for(int v:s.answer)cout<<" "<<v;cout<<endl;}return yes;
 }
 bool trunk(const vector<int>&opts,int first,const Small&one,const Small&two,int edges){
  nodes++;int need=9-bs.size(),n=opts.size();
  for(int j=first;j+need<=n;j++){
   int g=opts[j],lo=edges;for(int t=j;t<j+need;t++)lo+=wt[opts[t]];if(lo>N+7)break;
   array<int,4>poss{};int num=-1;bs.push_back(g);bool bad=false;
   for(int k=0;k<8&&!bad;k++){auto z=two.z[k]&hit[g].z[k];while(z){int v=64*k+countr_zero(z);z&=z-1;
      if(num<0){num=1;poss[0]=v;for(int a:bs)if(membership[v^a])poss[num++]=v^a;assert(num==4);}
      else{int keep=0;for(int q=0;q<num;q++){int x=poss[q];if(x==v||find(bs.begin(),bs.end(),x^v)!=bs.end())poss[keep++]=x;}num=keep;if(!num){bad=true;break;}}
   }}
   if(num<0){
     if(need==1){if(edges+wt[g]>=N-2-mh)for(int x:p)if(fixed(x,opts,j+1))return true;}
     else{Small a,b;for(int k=0;k<8;k++){a.z[k]=one.z[k]^hit[g].z[k];b.z[k]=two.z[k]|(one.z[k]&hit[g].z[k]);}if(trunk(opts,j+1,a,b,edges+wt[g]))return true;}
   }else for(int i=0;i<num;i++)if(fixed(poss[i],opts,j+1))return true;
   bs.pop_back();
  }return false;
 }
 bool solve(){vector<int> opts(511);iota(opts.begin(),opts.end(),1);sort(opts.begin(),opts.end(),[&](int a,int b){return pair(wt[a],a)<pair(wt[b],b);});return trunk(opts,0,Small{},Small{},0);}
};
int main(int argc,char**argv){int cap=argc>1?atoi(argv[1]):1000000,tests=0;string line;while(getline(cin,line)){istringstream ss(line);int r,m,b,n,x;ss>>r>>m>>b>>n;vector<int>P;while(ss>>x)P.push_back(x);if(n<194||n>198)continue;if(tests++>=cap)break;vector<int> ts;for(int t:{192,195,196})if(n<=t+2)ts.push_back(t);OneDrop e(P,ts);bool f=e.solve();cout<<r<<" "<<m<<" "<<b<<" "<<n<<" "<<(f?"FOUND":"CLOSED")<<" "<<e.nodes<<" "<<e.fixcalls<<" "<<e.fixnodes<<endl;if(f)return 0;}}
