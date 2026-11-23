// For a fixed 96-point parity class, enumerate two additions after one or two
// removals. The opposite parity class and its Hamiltonian order remain free.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <set>
#include <sstream>
int main(int argc,char**argv){
 if(argc!=2)return 2;bool maj=stoi(argv[1])==1;
 string line;set<vector<int>> seen;uint64_t models=0,low=0,dead=0,unknown=0,roots=0,cut=0;
 while(getline(cin,line)){
  istringstream in(line);vector<int>p,a;int x;while(in>>x)p.push_back(x);
  for(int i=1;i<(int)p.size();i+=2)a.push_back(p[i]);
  sort(a.begin(),a.end());if(!seen.insert(a).second)continue;
  vector<int> extra;for(int v=0;v<512;v++)if(!(__builtin_popcount(v^a[0])%2)&&!binary_search(a.begin(),a.end(),v))extra.push_back(v);
  for(int i=0;i<(int)a.size();i++)for(int j=maj?-1:0;j<(maj?0:i);j++){
   roots++;vector<int>b;for(int k=0;k<(int)a.size();k++)if(k!=i&&k!=j)b.push_back(a[k]);
   Search s(b,100000,maj);bool pass=true;int one=0;
   for(int v:b){int room=0;for(int d=0;d<9;d++)room+=__builtin_popcount(unsigned(s.axes[v^(1<<d)]))<=2;
    if(!room||(!maj&&room<2)){pass=false;break;}one+=(room==1);}
   if(!pass||(maj&&one>2)){cut++;continue;}
   vector<int>c;for(int v:extra){int room=0;for(int d=0;d<9;d++)room+=__builtin_popcount(unsigned(s.axes[v^(1<<d)]))<=1;if(room>=(maj?1:2))c.push_back(v);}
   int f=b.size();s.fixed.resize(f+2);
   for(int u=0;u<(int)c.size();u++){
    s.fixed[f]=c[u];s.toggle(c[u],f,true);
    for(int v=0;v<u;v++){
     s.fixed[f+1]=c[v];s.toggle(c[v],f+1,true);if(s.test())return 0;s.toggle(c[v],f+1,false);
    }
    s.toggle(c[u],f,false);
   }
   models+=s.tested;low+=s.low;dead+=s.dead;unknown+=s.unknown;
  }
 }
 cout<<"DONE mode "<<(maj?"one_remove":"two_remove")<<" sets "<<seen.size()<<" removals "<<roots<<" pruned "<<cut<<" tested "<<models<<" low "<<low<<" exhausted "<<dead<<" unknown "<<unknown<<endl;
}
