// Given two aligned parity sets A,B, retain A intersect B and freely choose
// any remaining vertices from A union B. Reconstruct the other parity freely.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <set>
#include <sstream>
#include <random>
#include <numeric>
struct Mixer{
 Search s;bool maj;int size,cap;uint64_t nodes=0,tests=0,unknown=0;bool capped=false;
 Mixer(vector<int> fixed,bool m,int goal,int cap_):s(fixed,30000,m),maj(m),size(goal),cap(cap_){}
 bool go(vector<int> candidates){
  if(nodes>=unsigned(cap)){capped=true;return false;}nodes++;
  int need=size-s.fixed.size();
  if(need==0){tests++;if(s.test())return true;unknown=s.unknown;return false;}
  int one=0;
  for(int v:s.fixed){int room=0;for(int d=0;d<9;d++)room+=__builtin_popcount(unsigned(s.axes[v^(1<<d)]))<=2;
  if(!room||(!maj&&room<2)||(maj&&room==1&&++one>2))return false;}
  vector<int> choices;
  for(int v:candidates){int room=0;for(int d=0;d<9;d++)room+=__builtin_popcount(unsigned(s.axes[v^(1<<d)]))<=1;
  if(room>=(maj?1:2))choices.push_back(v);}
  if(int(choices.size())<need)return false;
  int pos=s.fixed.size(),v=choices.back();choices.pop_back();
  s.fixed.push_back(v);s.toggle(v,pos,true);if(go(choices))return true;s.toggle(v,pos,false);s.fixed.pop_back();
  if(int(choices.size())>=need&&!capped&&go(choices))return true;
  return false;
 }
};
int main(int argc,char**argv){
 if(argc!=4)return 2;bool maj=atoi(argv[1]);int maxpairs=atoi(argv[2]),cap=atoi(argv[3]);
 vector<vector<int>>bank;set<vector<int>>seen;string line;
 while(getline(cin,line)){istringstream in(line);vector<int>p,q;int x;while(in>>x)p.push_back(x);
 for(int i=maj?0:1;i<(int)p.size();i+=2)q.push_back(p[i]);sort(q.begin(),q.end());if(seen.insert(q).second)bank.push_back(q);}
 struct Pair{int i,j,shift,edits;};vector<Pair>pairs;
 for(int i=0;i<(int)bank.size();i++)for(int j=0;j<i;j++){
 array<int,512> freq{};for(int u:bank[i])for(int v:bank[j])freq[u^v]++;
 vector<int> shifts(512);iota(shifts.begin(),shifts.end(),0);stable_sort(shifts.begin(),shifts.end(),[&](int a,int b){return freq[a]>freq[b];});
 for(int shift:shifts){int d=bank[i].size()-freq[shift];if(d>30)break;if(d>=2){pairs.push_back({i,j,shift,d});break;}}
 }
 mt19937 gen(88741);shuffle(pairs.begin(),pairs.end(),gen);int done=0,limited=0;uint64_t nodes=0,tests=0,unknown=0;
 for(auto t:pairs){
 if(done==maxpairs)break;set<int>b;for(int v:bank[t.j])b.insert(v^t.shift);vector<int> common,diff;
 for(int v:bank[t.i]){if(b.erase(v))common.push_back(v);else diff.push_back(v);}diff.insert(diff.end(),b.begin(),b.end());shuffle(diff.begin(),diff.end(),gen);
 Mixer m(common,maj,bank[t.i].size(),cap);if(m.go(diff)){cout<<"PAIR "<<t.i<<" "<<t.j<<" shift "<<t.shift<<endl;return 0;}
 done++;nodes+=m.nodes;tests+=m.tests;unknown+=m.unknown;limited+=m.capped;if(done%100==0)cout<<"STEP "<<done<<" capped "<<limited<<" nodes "<<nodes<<" leaves "<<tests<<endl;
 }
 cout<<"DONE sets "<<bank.size()<<" eligible_pairs "<<pairs.size()<<" tested_pairs "<<done<<" capped "<<limited<<" nodes "<<nodes<<" full_sets "<<tests<<" hamilton_unknown "<<unknown<<endl;
}
