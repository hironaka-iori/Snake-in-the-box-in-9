#include <fstream>
#include <unordered_set>
#include <string>
// Exact fixed-size vertex exchange around a single induced path.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <vector>
using namespace std;
unordered_set<string> blockedFragments;
bool passes_fragments(const vector<int>& p){
    if(blockedFragments.empty())return true;
    for(int i=0;i+142<int(p.size());i++){
       string forward;
       for(int reverse=0;reverse<2;reverse++){
          int labels[9];fill_n(labels,9,-1);int count=0;string key;
          for(int h=0;h<142;h++){
             int j=i+(reverse?141-h:h);
             int d=countr_zero(unsigned(p[j]^p[j+1]));
             if(labels[d]<0)labels[d]=count++;
             key+=char('0'+labels[d]);
          }
          if(!reverse)forward=key;
          else if(blockedFragments.contains(min(key,forward)))return false;
       }
    }
    return true;
}
struct Exchange {
 int n,dim,k,N,gain=1;bool emitAll=false,fastPairs=false;
 vector<int> p,removed,chosen,witness,outside;
 array<int,512> idx{},degree{};
 array<bool,512> active{};
 uint64_t tested=0,viable=0,trials=0;
 void toggle(int v,bool on){active[v]=on;for(int j=0;j<dim;j++) degree[v^(1<<j)]+=on?1:-1;}
 bool valid(const vector<int>& path) const{
   for(int i=0;i<(int)path.size();++i){
     if(path[i]<0||path[i]>=N)return false;
     for(int j=0;j<i;j++)if(path[i]==path[j]||(popcount(unsigned(path[i]^path[j]))==1)!=(j+1==i))return false;
   }
   return true;
 }
 bool finish(){
   trials++;int end=-1,ends=0;
   auto inspect=[&](int x){
      if(degree[x]==1){end=x;ends++;}return degree[x]==1||degree[x]==2;
   };
   for(int x:p)if(active[x]&&!inspect(x))return false;
   for(int x:chosen)if(!inspect(x))return false;
   if(ends!=2)return false;
   vector<int> path;int prev=-1;
   while(end>=0){
      path.push_back(end);int next=-1;
      for(int j=0;j<dim;j++){int u=end^(1<<j);if(active[u]&&u!=prev){next=u;break;}}
      prev=end;end=next;
   }
   if(int(path.size())!=n+gain)return false;
   if(!valid(path))abort();if(!passes_fragments(path))return false;
   if(emitAll){cout<<"PATH";for(int v:path)cout<<" "<<v;cout<<endl;return false;}
   witness=path;return true;
 }
 bool add(const vector<int>& options,int start,int need){
    if(!need)return finish();
    for(int i=start;i+need<=(int)options.size();i++){
      int x=options[i];if(degree[x]>2)continue;
      bool ok=true;for(int j=0;j<dim;j++){int u=x^(1<<j);if(active[u]&&degree[u]>=2){ok=false;break;}}
      if(!ok)continue;
      toggle(x,true);chosen.push_back(x);
      if(add(options,i+1,need-1))return true;
      chosen.pop_back();toggle(x,false);
    }
    return false;
 }
 bool last(int start){
   vector<int> free;array<vector<int>,512> contingent;
   for(int x:outside){
     if(degree[x]>3)continue;
     int block[9],bn=0,neigh[9],nn=0;
     for(int j=0;j<dim;j++){
       int u=x^(1<<j);if(active[u]){neigh[nn++]=idx[u];if(degree[u]==2)block[bn++]=idx[u];}
     }
     if(!bn&&nn<=2){free.push_back(x);continue;}
     if(bn>=4)continue;
     auto accept=[&](int i){
       if(i<start||i>=n||!active[p[i]])return;
       if(nn==3&&popcount(unsigned(x^p[i]))!=1)return;
       for(int j=0;j<bn;j++)if(abs(block[j]-i)>1)return;
       contingent[i].push_back(x);
     };
     if(bn)for(int i=block[0]-1;i<=block[0]+1;i++)accept(i);
     else for(int j=0;j<nn;j++)accept(neigh[j]);
   }
   for(int i=start;i<n;i++){
     tested++;
     if(int(free.size()+contingent[i].size())<k+gain)continue;
     vector<int> options=free;options.insert(options.end(),contingent[i].begin(),contingent[i].end());
     toggle(p[i],false);removed.push_back(i);
     // Only path endpoints and the neighbors of deletions can have a deficit.
     vector<int> terminal{0,n-1};
     for(int d:removed){if(d)terminal.push_back(d-1);if(d+1<n)terminal.push_back(d+1);}
     sort(terminal.begin(),terminal.end());terminal.erase(unique(terminal.begin(),terminal.end()),terminal.end());
     int deficit=0;
     for(int t:terminal)if(active[p[t]]&&degree[p[t]]<2){
       int capacity=degree[p[t]];
       for(int x:options)capacity+=popcount(unsigned(p[t]^x))==1;
       deficit+=max(0,2-capacity);
     }
     if(deficit<=2){viable++;if(add(options,0,k+gain))return true;}
     removed.pop_back();toggle(p[i],true);
   }
   return false;
 }
 // Compute exactly which external vertices can be made available by the final two deletions.
 bool last_two(int start){
   vector<int> base;array<vector<int>,512> singles;
   vector<pair<int,int>> doubleHits;
   vector<int> ids;
   for(int x:outside){
     if(degree[x]>4)continue;
     int adj[9],bads[9],nn=0,bn=0;
     for(int j=0;j<dim;j++){
        int u=x^(1<<j);if(active[u]){adj[nn++]=idx[u];if(degree[u]==2)bads[bn++]=idx[u];}
     }
     if(!bn&&nn<=2){base.push_back(x);continue;}
     if(bn>6)continue;
     vector<int> one,two;
     auto enumerate=[&](auto&& self,int a,int b)->void{
       int missing=-1,left=0;
       for(int j=0;j<bn;j++)if((a<0||abs(bads[j]-a)>1)&&(b<0||abs(bads[j]-b)>1)){missing=bads[j];break;}
       for(int j=0;j<nn;j++)left+=adj[j]!=a&&adj[j]!=b;
       if(missing<0&&left<=2){
         if(b<0)one.push_back(a);
         else two.push_back(min(a,b)*n+max(a,b));
         return;
       }
       if(b>=0)return;
       auto choose=[&](int d){
          if(d>=start&&d<n&&d!=a&&active[p[d]])self(self,a<0?d:a,a<0?-1:d);
       };
       if(missing>=0){for(int d=missing-1;d<=missing+1;d++)choose(d);}
       else for(int j=0;j<nn;j++)choose(adj[j]);
     };
     enumerate(enumerate,-1,-1);
     sort(one.begin(),one.end());one.erase(unique(one.begin(),one.end()),one.end());
     for(int d:one)singles[d].push_back(x);
     sort(two.begin(),two.end());two.erase(unique(two.begin(),two.end()),two.end());
     for(int code:two)if(!binary_search(one.begin(),one.end(),code/n)&&!binary_search(one.begin(),one.end(),code%n))
        doubleHits.emplace_back(code,x);
   }
   int need=k+gain-int(base.size());
   vector<int> nonempty;
   for(int i=start;i<n;i++)if(!singles[i].empty())nonempty.push_back(i);
   if(need<=0){
      for(int i=start;i<n;i++)for(int j=i+1;j<n;j++)ids.push_back(i*n+j);
   }else{
      for(int i:nonempty){
        if(int(singles[i].size())>=need)for(int j=start;j<n;j++){if(i!=j)ids.push_back(min(i,j)*n+max(i,j));}
        else for(int j:nonempty)if(i<j&&int(singles[i].size()+singles[j].size())>=need)ids.push_back(i*n+j);
      }
   }
   sort(doubleHits.begin(),doubleHits.end());
   for(size_t l=0;l<doubleHits.size();){
      int code=doubleHits[l].first;size_t h=l+1;
      while(h<doubleHits.size()&&doubleHits[h].first==code)h++;
      if(int(h-l+singles[code/n].size()+singles[code%n].size())>=need)ids.push_back(code);
      l=h;
   }
   tested+=uint64_t(n-start)*(n-start-1)/2;
   sort(ids.begin(),ids.end());ids.erase(unique(ids.begin(),ids.end()),ids.end());
   for(int code:ids){
      int a=code/n,b=code%n;
      vector<int> options=base;
      for(int d:{a,b})options.insert(options.end(),singles[d].begin(),singles[d].end());
      auto it=lower_bound(doubleHits.begin(),doubleHits.end(),make_pair(code,-1));
      while(it!=doubleHits.end()&&it->first==code){options.push_back(it->second);++it;}
      sort(options.begin(),options.end());options.erase(unique(options.begin(),options.end()),options.end());
      if(int(options.size())<k+gain)continue;
      for(int d:{a,b}){toggle(p[d],false);removed.push_back(d);}
      vector<int> terminal{0,n-1};
      for(int d:removed){if(d)terminal.push_back(d-1);if(d+1<n)terminal.push_back(d+1);}
      sort(terminal.begin(),terminal.end());terminal.erase(unique(terminal.begin(),terminal.end()),terminal.end());
      int deficit=0;
      for(int t:terminal)if(active[p[t]]&&degree[p[t]]<2){
        int capacity=degree[p[t]];
        for(int x:options)capacity+=popcount(unsigned(p[t]^x))==1;
        deficit+=max(0,2-capacity);
      }
      if(deficit<=2){viable++;if(add(options,0,k+gain))return true;}
      for(int d:{b,a}){removed.pop_back();toggle(p[d],true);}
   }
   return false;
 }
 bool remove_first(int start,int left){
   if(fastPairs&&left==2)return last_two(start);
   if(left==1)return last(start);
   for(int i=start;i+left<=n;i++){
      toggle(p[i],false);removed.push_back(i);
      if(remove_first(i+1,left-1))return true;
      removed.pop_back();toggle(p[i],true);
   }
   return false;
 }
 bool run(){
    n=p.size();N=1<<dim;
    if(!valid(p)||k<1||k>=n)return false;
    idx.fill(-1);
    for(int i=0;i<n;i++){idx[p[i]]=i;toggle(p[i],true);}
    for(int i=0;i<N;i++)if(!active[i])outside.push_back(i);
    return remove_first(0,k);
 }
};
int main(int argc,char**argv){
 if(const char* f=getenv("Q9_AVOID_SHAPES")){
    ifstream in(f);string k;while(in>>k)blockedFragments.insert(k);
    if(blockedFragments.size()!=17974)return 4;
 }
 if(argc!=3&&argc!=4)return 1;string l;int row=0;
 while(getline(cin,l)){
    Exchange s{};s.dim=stoi(argv[1]);s.k=stoi(argv[2]);if(argc==4&&string(argv[3])=="--fast-pairs")s.fastPairs=true;else if(argc==4){s.emitAll=true;string mode=argv[3];if(mode.starts_with("--all-fast=")){s.fastPairs=true;mode=mode.substr(11);}s.gain=stoi(mode);if(s.gain<0||s.gain>1)return 2;}if(s.dim<1||s.dim>9)return 2;
    istringstream in(l);int v;while(in>>v)s.p.push_back(v);
    bool found=s.run();
    cout<<row++<<" "<<(found?"FOUND":"NO")<<" "<<s.tested<<" "<<s.viable<<" "<<s.trials;
    for(int x:s.witness)cout<<" "<<x;cout<<endl;
 }
}
