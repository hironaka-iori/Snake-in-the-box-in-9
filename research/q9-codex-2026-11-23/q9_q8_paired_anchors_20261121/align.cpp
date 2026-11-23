#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Node{array<int,8> child{};short mother=-1; signed char shift=-1;};
struct Seed{int donor,off,mother,shift,n;string pick;};
vector<Node> nodes(1);vector<string> bank,mother;
vector<Seed> reservoir,best;mt19937 rg(781309);long long hits=0,visits=0;int maxlen=0,archiveRow,offset;string picked;array<int,9> mp;
void walk(int nd,int k,int next){
 ++visits;auto &s=bank[archiveRow];int t=offset+2*k;bool found=false;
 if(t+1<(int)s.size())for(int a=0;a<2;a++){
  int d=s[t+a]-'0';bool fresh=mp[d]<0;int v=fresh?next:mp[d];if(v>=8||!nodes[nd].child[v])continue;
  found=true;if(fresh)mp[d]=next;picked+=char('0'+d);walk(nodes[nd].child[v],k+1,next+fresh);picked.pop_back();if(fresh)mp[d]=-1;
 }
 if(found||k<1)return;
 if(k>=best[archiveRow].n||k>=16){Seed e{archiveRow,offset,nodes[nd].mother,nodes[nd].shift,k,picked};
  if(k>best[archiveRow].n)best[archiveRow]=e;
  if(k>maxlen){maxlen=k;cerr<<"new_best "<<k<<" donor "<<archiveRow<<" offset "<<offset<<endl;}
  if(k>=16){++hits;if(reservoir.size()<8000)reservoir.push_back(e);else{long long i=uniform_int_distribution<long long>(0,hits-1)(rg);if(i<(int)reservoir.size())reservoir[i]=e;}}
 }
}
int main(){
 string w;ifstream a("../q8_catalogue_96_98.words"),b("../q9_gap_generations/prior191.words");ofstream mr("mothers.tsv");
 int rid=0;while(a>>w){for(int rev=0;rev<2;rev++){for(int j=0;j+96<=(int)w.size();j++){auto s=w.substr(j,96);int id=mother.size();mother.push_back(s);mr<<id<<' '<<rid<<' '<<rev<<' '<<j<<' '<<s<<'\n';
   for(int st=0;st<96;st++){array<int,8> p;p.fill(-1);int k=0,nd=0;for(int t=st;t<96;t++){int d=s[t]-'0';if(p[d]<0)p[d]=k++;int ix=p[d];if(!nodes[nd].child[ix]){int v=nodes.size();nodes[nd].child[ix]=v;nodes.emplace_back();}
   nd=nodes[nd].child[ix];if(nodes[nd].mother<0 || int(rg()%12)==0){nodes[nd].mother=id;nodes[nd].shift=st;}}}}
  reverse(w.begin(),w.end());}rid++;}
 while(b>>w)bank.push_back(w);best.resize(bank.size());for(auto &r:best)r.n=0;
 for(archiveRow=0;archiveRow<(int)bank.size();archiveRow++)for(offset=0;offset+1<(int)bank[archiveRow].size();offset++){mp.fill(-1);picked.clear();walk(0,0,0);}
 auto save=[](string f,const vector<Seed>&v){ofstream o(f);for(auto &s:v)o<<s.donor<<' '<<s.off<<' '<<s.mother<<' '<<s.shift<<' '<<s.n<<' '<<s.pick<<'\n';};
 save("best.tsv",best);save("sample.tsv",reservoir);cout<<"mothers "<<mother.size()<<" trie_nodes "<<nodes.size()<<" bank "<<bank.size()<<" visits "<<visits<<" maximal_terminal_matches_ge16 "<<hits<<" longest "<<maxlen<<endl;
}
