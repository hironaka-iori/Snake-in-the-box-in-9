#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using M=__uint128_t;using M4=array<uint64_t,4>;
struct State{bool live[256]{};int degree[256]{};P arms[2];};
bool parse(State&s,const string&line){istringstream in(line);for(int j=0;j<2;j++){int n;if(!(in>>n))return false;int x;for(int i=0;i<n;i++){in>>x;s.arms[j].push_back(x);s.live[x]=true;for(int d=0;d<8;d++)s.degree[x^(1<<d)]++;}}return true;}
int rowCap;
long long placements,fit,pv,extended;int best;set<M4> output,seen;vector<State> frontier;
void emit(State&s){
 int n=int(s.arms[0].size()+s.arms[1].size());if(n<100)return;M4 m{};for(auto&p:s.arms)for(int x:p)m[x/64]|=1ull<<(x%64);
 if(!output.insert(m).second)return;best=max(best,n);int offset=s.arms[0][0];for(auto&p:s.arms){cout<<p.size();for(int x:p)cout<<" "<<(x^offset);cout<<" ";}cout<<endl;
 if(frontier.size()<rowCap)frontier.push_back(s);
}
array<array<int,256>,40320> table;
void piv(const State&src){
 for(int which=0;which<2;which++)for(int rev=0;rev<2;rev++){auto a=src.arms[which];if(rev)reverse(a.begin(),a.end());const auto&b=src.arms[1-which];
  for(int cut=2;cut+2<a.size();cut++){
   int center=a[cut];bool blocked[256]{};for(int x:b){blocked[x]=true;for(int d=0;d<8;d++)blocked[x^(1<<d)]=true;}
   for(int i=0;i<cut;i++){int x=a[i];blocked[x]=true;for(int d=0;d<8;d++)blocked[x^(1<<d)]=true;}blocked[center]=true;
   P rel;for(int i=cut+1;i<a.size();i++)rel.push_back(a[i]^center);
   for(const auto&tab:table){++placements;bool ok=true;for(auto u:rel)if(blocked[center^tab[u]]){ok=false;break;}if(!ok)continue;
    P arm(a.begin(),a.begin()+cut+1);for(int u:rel)arm.push_back(center^tab[u]);M4 state{};for(int x:b)state[x/64]|=1ull<<(x%64);for(int x:arm)state[x/64]|=1ull<<(x%64);
    if(!seen.insert(state).second)continue;++fit;State s;s.arms[0]=arm;s.arms[1]=b;for(auto &w:s.arms)for(int v:w){s.live[v]=true;for(int d=0;d<8;d++)s.degree[v^(1<<d)]++;}
    emit(s);
    for(int j=0;j<2;j++)for(int side:{0,1}){int tip=side?s.arms[j].back():s.arms[j].front();
      for(int d=0;d<8;d++){int y=tip^(1<<d);if(s.live[y]||s.degree[y]!=1)continue;State t=s;
       if(side)t.arms[j].push_back(y);else t.arms[j].insert(t.arms[j].begin(),y);t.live[y]=true;for(int h=0;h<8;h++)t.degree[y^(1<<h)]++;emit(t);++extended;
      }
    }
   }
  }
 }
}
int main(int argc,char**argv){if(argc!=2)return 2;rowCap=stoi(argv[1]);array<int,8> pi{0,1,2,3,4,5,6,7};int k=0;do{auto&t=table[k++];for(int u=1;u<256;u++)t[u]=t[u&(u-1)]|(1<<pi[countr_zero(unsigned(u))]);}while(next_permutation(pi.begin(),pi.end()));string line;while(getline(cin,line)){State s;if(!parse(s,line))return 3;frontier.push_back(s);}for(int k=0;k<frontier.size()&&k<rowCap;k++){State s=frontier[k];piv(s);}cerr<<"placements "<<placements<<" raw_states "<<fit<<" extra_vertices "<<extended<<" best "<<best<<" frontierd "<<frontier.size()<<endl;}
