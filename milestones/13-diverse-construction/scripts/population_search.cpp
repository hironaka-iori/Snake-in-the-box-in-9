// Population variant of milestone 12, retaining symmetry-distinct equal-score walks.
// Fixed-length nearest-neighbor walks with soft penalties for duplicate vertices
// and nonconsecutive adjacencies. Outputs are research data, not certificates.
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
#include <set>
using namespace std;
static constexpr int N=512, D=9, DUP=4;
bool adjacent(int a,int b) { int d=a^b; return d && !(d&(d-1)); }
struct Defects { int duplicates=0,chords=0; int energy() const{return DUP*duplicates+chords;} };
Defects check(const vector<int>& p) {
  Defects out;
  for(int i=0;i<(int)p.size();++i) {
    assert(0<=p[i] && p[i]<N);
    if(i) assert(adjacent(p[i-1],p[i]));
    for(int j=0;j<i;++j) {
      if(p[i]==p[j]) ++out.duplicates;
      if(i>j+1 && adjacent(p[i],p[j])) ++out.chords;
    }
  }
  return out;
}
array<int,N> field(const vector<int>& p) {
  array<int,N> f{};
  for(int v:p) { f[v]+=DUP; for(int k=0;k<D;++k) ++f[v^(1<<k)]; }
  return f;
}
// Only cross pairs can change when a contiguous interval is translated by XOR.
int delta(const vector<int>& p,const array<int,N>& f,int lo,int hi,int mask) {
  array<int,N> local{};
  for(int i=lo;i<=hi;++i) {
    int v=p[i]; local[v]+=DUP;
    for(int k=0;k<D;++k) ++local[v^(1<<k)];
  }
  int d=0;
  for(int i=lo;i<=hi;++i) {
    int v=p[i],w=v^mask;
    d+=(f[w]-local[w])-(f[v]-local[v]);
  }
  return d;
}
void apply(vector<int>& p,array<int,N>& f,int lo,int hi,int mask) {
  for(int i=lo;i<=hi;++i) {
    int v=p[i],w=v^mask; f[v]-=DUP; f[w]+=DUP;
    for(int k=0;k<D;++k) { --f[v^(1<<k)]; ++f[w^(1<<k)]; }
    p[i]=w;
  }
}
vector<int> longest_segment(const vector<int>& p) {
  int start=0,best=0,len=1;
  for(int j=1;j<(int)p.size();++j) {
    for(int i=start;i<j;++i)
      if(p[i]==p[j] || (i+1<j && adjacent(p[i],p[j]))) start=max(start,i+1);
    if(j-start+1>len) {best=start;len=j-start+1;}
  }
  return vector<int>(p.begin()+best,p.begin()+best+len);
}
void emit_array(ostream& f,const vector<int>& p) {
  f<<'['; for(size_t i=0;i<p.size();++i) {if(i)f<<',';f<<p[i];} f<<']';
}
// Translation, coordinate permutation, and reversal invariant transition key.
string canonical_key(const vector<int>& p) {
  auto key=[](vector<int> q) {
    array<int,512> names{}; names.fill(-1); int next=0; string k;
    for(size_t i=1;i<q.size();++i) {
      int d=q[i]^q[i-1]; if(names[d]<0)names[d]=next++;
      k.push_back(char('0'+names[d]));
    }
    return k;
  };
  auto q=p; reverse(q.begin(),q.end()); return min(key(p),key(q));
}
int main(int argc,char** argv) {
  string input,output; int target=196,seed=13,seed_index=0; double seconds=30;
  bool audit=false; int capacity=32; long long budget=5000000;
  for(int i=1;i<argc;++i) {
    string a=argv[i];
    if(a=="--audit") audit=true;
    else if(i+1<argc) {
      string v=argv[++i];
      if(a=="--input")input=v; else if(a=="--output")output=v;
      else if(a=="--target")target=stoi(v); else if(a=="--seed")seed=stoi(v);
      else if(a=="--seed-index")seed_index=stoi(v); else if(a=="--seconds")seconds=stod(v);
      else if(a=="--capacity")capacity=stoi(v); else if(a=="--proposals")budget=stoll(v);
      else {cerr<<"Unknown option\n";return 2;}
    } else return 2;
  }
  if(input.empty()||output.empty()||target<1||seconds<=0||capacity<1||budget<1) return 2;
  vector<vector<int>> bank; ifstream in(input); string line;
  while(getline(in,line)) {istringstream s(line);vector<int> p;int v;while(s>>v)p.push_back(v);if(!p.empty())bank.push_back(p);}
  if(bank.empty()||seed_index<0||seed_index>=(int)bank.size())return 2;
  for(const auto& p:bank)assert(check(p).energy()==0);
  mt19937 rng(seed); uniform_real_distribution<double> uniform(0.0,1.0);
  auto make_start=[&](int index) {
    vector<int> p=bank[index];
    if(rng()%2)reverse(p.begin(),p.end());
    if((int)p.size()>target+1)p.resize(target+1);
    while((int)p.size()<target+1) {
      // Try all legal coordinate steps; choose among the least defective additions.
      int best=100000; vector<int> ties;
      for(int k=0;k<D;++k) {
        int w=p.back()^(1<<k),cost=0;
        for(size_t j=0;j<p.size();++j) {
          cost+=DUP*(p[j]==w); if(j+1<p.size())cost+=adjacent(p[j],w);
        }
        if(cost<best){best=cost;ties.clear();}if(cost==best)ties.push_back(w);
      }
      p.push_back(ties[rng()%ties.size()]);
    }
    return p;
  };
  vector<int> p=make_start(seed_index),best_walk=p,best_valid=longest_segment(p);
  auto f=field(p);int energy=check(p).energy(),best_energy=energy,initial_energy=energy;
  long long proposals=0,accepted=0,checks=0,restarts=0;
  vector<vector<int>> pool{p};set<string> seen{canonical_key(p)};
  mt19937 pool_rng(seed^0x196196u);
  auto retain=[&]() {
    string key=canonical_key(p);
    if(!seen.insert(key).second || capacity==1)return;
    if((int)pool.size()<capacity)pool.push_back(p);
    else {size_t k=pool_rng()%seen.size();if(k<pool.size())pool[k]=p;}
  };
  auto begin=chrono::steady_clock::now();double elapsed=0;
  auto save=[&]() {
    auto b=check(best_walk);assert(b.energy()==best_energy);assert(check(best_valid).energy()==0);
    ofstream out(output);
    out<<"{\n\"capacity\":"<<capacity<<",\"proposal_budget\":"<<budget<<",\"best_score_classes_seen\":"<<seen.size()<<",\"pool_size\":"<<pool.size()<<",";
    out<<"\n\"target_edges\":"<<target<<",\"seed\":"<<seed<<",\"seed_index\":"<<seed_index
       <<",\"seconds\":"<<elapsed<<",\"proposals\":"<<proposals<<",\"accepted\":"<<accepted
       <<",\"delta_audits\":"<<checks<<",\"restarts\":"<<restarts<<",\"duplicate_weight\":"<<DUP
       <<",\"initial_energy\":"<<initial_energy<<",\"best_energy\":"<<best_energy
       <<",\"duplicate_pairs\":"<<b.duplicates<<",\"chord_pairs\":"<<b.chords
       <<",\"status\":\""<<(best_energy==0?"CANDIDATE_REQUIRES_INDEPENDENT_CHECK":"NO_WITNESS")
       <<"\",\"best_valid_edges\":"<<best_valid.size()-1<<",\"best_walk\":";
    emit_array(out,best_walk);out<<",\"best_valid_segment\":";emit_array(out,best_valid);out<<",\"pool\":[";
    for(size_t k=0;k<pool.size();++k) {assert(check(pool[k]).energy()==best_energy);if(k)out<<',';emit_array(out,pool[k]);}
    out<<"]}\n";
  };
  while(elapsed<seconds && proposals<budget && best_energy>0) {
    ++proposals;
    int i=rng()%target,j=target,mask;
    int a=p[i]^p[i+1];
    if(rng()%100<70) {
      j=rng()%target;if(i>j)swap(i,j);
      if(i==j)continue;
      a=p[i]^p[i+1];int b=p[j]^p[j+1];if(a==b)continue;
      mask=a^b; // Swap the directions of the two boundary transitions.
    } else {
      int b=1<<(rng()%D);if(a==b)continue;mask=a^b;
    }
    int lo=i+1,hi=j;
    int change=delta(p,f,lo,hi,mask);
    if(audit || proposals%5000==0) {
      auto q=p;for(int h=lo;h<=hi;++h)q[h]^=mask;
      assert(check(q).energy()-check(p).energy()==change);++checks;
    }
    double phase=double(proposals%200000)/200000.0;
    double temperature=1.8*pow(0.035/1.8,phase);
    if(change<=0 || uniform(rng)<exp(-double(change)/temperature)) {
      apply(p,f,lo,hi,mask);energy+=change;++accepted;
      if(energy<best_energy) {
        best_energy=energy;best_walk=p;pool={p};seen={canonical_key(p)};
        auto segment=longest_segment(p);if(segment.size()>best_valid.size())best_valid=segment;
      } else if(energy==best_energy)retain();
    }
    if(proposals%5000==0) {
      assert(check(p).energy()==energy);assert(field(p)==f);
      auto segment=longest_segment(p);if(segment.size()>best_valid.size())best_valid=segment;
      elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();if(proposals%100000==0)save();
    }
    if(proposals%200000==0) {
      ++restarts;
      p=(rng()%3==0)?make_start(rng()%bank.size()):pool[capacity==1?0:rng()%pool.size()];
      energy=check(p).energy();f=field(p);
    }
    // Poll elapsed time also when auditing, which intentionally runs much slower.
    if(audit && proposals%100==0)elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();
  }
  elapsed=chrono::duration<double>(chrono::steady_clock::now()-begin).count();save();
  cout<<"target="<<target<<" best_energy="<<best_energy<<" valid_edges="<<best_valid.size()-1
      <<" proposals="<<proposals<<" seconds="<<elapsed<<'\n';
}
