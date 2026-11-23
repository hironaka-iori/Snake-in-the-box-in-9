// Look for two long Q8 paths at mutual Hamming distance at least two.
#define main old_beam_main
#include "search_q8_layer_beam.cpp"
#undef main
#include <bit>
#include <set>
#include <sstream>
using P=vector<int>;
struct Partner{
 P first,second;int target,budget,limit,nodes=0,saved=0;mt19937&gen;set<array<U,4>> seen;
 Partner(P a,int size,int cap,int lim,mt19937&r):first(std::move(a)),target(size-first.size()),budget(cap),limit(lim),gen(r){}
 void dfs(int v,Set avail,Set chosen){
  if(nodes++>=budget||saved>=limit)return;int n=second.size();
  if(n>=target){if(second.front()<v&&seen.insert(chosen.a).second){
    int org=first[0];cout<<first.size();for(int x:first)cout<<" "<<(x^org);cout<<" "<<second.size();for(int x:second)cout<<" "<<(x^org);cout<<"\n";saved++;}
   if(n>=target+2||saved>=limit)return;}
  if(n%4==1||n+8>=target){
   Set reach;reach.add(v);for(;;){Set nx=adjacent(reach);for(int j=0;j<4;j++)nx.a[j]=(nx.a[j]&avail.a[j])|reach.a[j];if(nx==reach)break;reach=nx;}
   int c[2]={};for(int j=0;j<4;j++){c[0]+=popcount(reach.a[j]&parity.a[j]);c[1]+=popcount(reach.a[j]&~parity.a[j]);}
   int b=__builtin_parity((unsigned)v),longest=min(2*c[b],2*c[1-b]+1);
   if(n-1+longest<target)return;for(int j=0;j<4;j++)avail.a[j]&=reach.a[j];}
  Set child=avail;for(int j=0;j<4;j++)child.a[j]&=~nbr[v].a[j];
  int start=gen()%8,odd=1+2*(gen()%4);
  for(int j=0;j<8&&nodes<budget&&saved<limit;j++){int x=v^1<<((start+odd*j)%8);if(!avail.has(x))continue;Set c=chosen;c.add(x);second.push_back(x);dfs(x,child,c);second.pop_back();}
 }
 void run(){if(target<2||target>80)return;Set free;free.a.fill(~U(0));for(int v:first){free.del(v);for(int j=0;j<4;j++)free.a[j]&=~nbr[v].a[j];}
  P starts;for(int x=0;x<256;x++)if(free.has(x))starts.push_back(x);shuffle(starts.begin(),starts.end(),gen);
  for(int x:starts){if(nodes>=budget||saved>=limit)break;Set a=free,c;c.add(x);a.del(x);second={x};dfs(x,a,c);}
 }
};
int main(int argc,char**argv){if(argc!=7)return 2;int size=stoi(argv[1]),budget=stoi(argv[2]),limit=stoi(argv[3]),trials=stoi(argv[4]),global=stoi(argv[5]);mt19937 rng(stoul(argv[6]));
 for(int i=0;i<256;i++){if(!__builtin_parity((unsigned)i))parity.add(i);for(int d=0;d<8;d++)nbr[i].add(i^(1<<d));}
 vector<P> donors;string line;while(getline(cin,line)){istringstream s(line);int n,x;while(s>>n){P a;for(int i=0;i<n;i++){s>>x;a.push_back(x);}if(a.size()>=39&&valid(a))donors.push_back(a);}}
 if(donors.empty())abort();int out=0;long long nodes=0;for(int t=0;t<trials&&out<global;t++){auto &p=donors[t<donors.size()?t:rng()%donors.size()];int n=p.size();int len=t<donors.size()?n:37+rng()%(n-36);int i=rng()%(n-len+1);
  P a(p.begin()+i,p.begin()+i+len);Partner b(a,size,budget,limit,rng);b.run();out+=b.saved;nodes+=b.nodes;if(t%100==0)cout.flush();}
 cerr<<"saved "<<out<<" visits "<<nodes<<" donors "<<donors.size()<<endl;
}
