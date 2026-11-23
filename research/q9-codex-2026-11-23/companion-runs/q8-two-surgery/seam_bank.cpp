#include <random>
// Assemble two Q7 slice forests at arbitrary cube isometries. Fix relative
// translation by a pair of crossing vertices; count all coordinate permutations.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;using P=vector<int>;using M=__uint128_t;
struct Half{vector<int>v;M occ=0,sat=0,singles=0;int edges=0,ends=0;bool purpose=false;};
void fill(Half&h){for(int x:h.v)h.occ|=M(1)<<x;for(int x:h.v){int d=0;for(int j=0;j<7;j++)d+=bool(h.occ&(M(1)<<(x^(1<<j))));h.edges+=d;if(d==2)h.sat|=M(1)<<x;else if(!d)h.singles|=M(1)<<x;if(d<2)++h.ends;}h.edges/=2;}
bool bit(M m,int x){return bool((m>>x)&1);}
int weight(M x){return popcount(uint64_t(x))+popcount(uint64_t(x>>64));}
unsigned long long tests=0,filtered=0,validN=0;set<array<uint64_t,4>> raw;
int baseMap[128];M ones[7];int maxN=0;
M shift(M s,int x){for(int d=0;d<7;d++)if(x>>d&1){int t=1<<d;s=((s&ones[d])>>t)|((s&~ones[d])<<t);}return s;}
string key(array<P,2> q){string best;for(int sw=0;sw<2;sw++){if(sw)swap(q[0],q[1]);for(int rev=0;rev<4;rev++){
 unsigned char m[8]{};int ctr=0;string s;for(int i=0;i<2;i++){auto&p=q[i];for(int j=1;j<p.size();j++){int h=(rev>>i&1)?p.size()-j:j;int d=countr_zero(unsigned(p[h]^p[h-1]));if(!m[d])m[d]=++ctr;s+=char(m[d]);}s+=':';}
 int off=q[0][rev&1?q[0].size()-1:0]^q[1][rev&2?q[1].size()-1:0],bits=0,other=0;for(int j=0;j<8;j++)if(off>>j&1){if(m[j])bits|=1<<(m[j]-1);else other++;}s+=char(bits);s+=char(other);if(best.empty()||s<best)best=s;}}return best;}
set<string> uniqueKeys;
void emit(M lo,M hi){array<uint64_t,4> m{uint64_t(lo),uint64_t(lo>>64),uint64_t(hi),uint64_t(hi>>64)};if(!raw.insert(m).second)return;
 array<M,2> bits{lo,hi};bool seen[256]{};array<P,2> q;int count=0,k=0;
 auto present=[&](int x){return bit(bits[x>>7],x&127);};
 for(int x=0;x<256;x++)if(present(x)&&!seen[x]){int d=0;for(int j=0;j<8;j++)d+=present(x^(1<<j));if(d>1)continue;if(k==2)return;int v=x,last=-1;while(v>=0){if(seen[v])return;seen[v]=true;count++;q[k].push_back(v);int w=-1;for(int j=0;j<8;j++){int u=v^(1<<j);if(u!=last&&present(u)){if(w>=0)return;w=u;}}last=v;v=w;}k++;}
 if(k!=2||count!=weight(lo)+weight(hi))return;++validN;if(!uniqueKeys.insert(key(q)).second)return;
 int z=q[0][0];for(auto&p:q){cout<<p.size();for(int v:p)cout<<" "<<(v^z);cout<<" ";}cout<<endl;maxN=max(maxN,count);
}
int main(int argc,char**argv){
 if(argc!=5)return 2;int anchored=stoi(argv[4]),sourceRow=0;int minN=stoi(argv[1]),maxRows=stoi(argv[2]),permStride=stoi(argv[3]);vector<Half> hs;set<M> seen;string line;
 while(getline(cin,line)){++sourceRow;istringstream s(line);int n;P a;while(s>>n){for(int j=0;j<n;j++){int x;if(!(s>>x)||x<0||x>255)return 3;a.push_back(x);}}
  for(int axis=0;axis<8;axis++)for(int side=0;side<2;side++){Half h;h.purpose=(anchored==0||sourceRow<=anchored);for(int x:a)if((x>>axis&1)==side)h.v.push_back((x&((1<<axis)-1))|((x>>(axis+1))<<axis));fill(h);if(!seen.insert(h.occ).second)continue;hs.push_back(h);}
 }
 for(int i=0;i<7;i++)for(int v=0;v<128;v++)if(v>>i&1)ones[i]|=M(1)<<v;
 if(hs.size()>maxRows){vector<Half> pri,rest;for(auto&h:hs)(h.purpose?pri:rest).push_back(h);shuffle(rest.begin(),rest.end(),mt19937(918721));if(pri.size()+rest.size()>maxRows)rest.resize(max(0,maxRows-int(pri.size())));pri.insert(pri.end(),rest.begin(),rest.end());hs=move(pri);}sort(hs.begin(),hs.end(),[](auto&a,auto&b){return a.v.size()>b.v.size();});
 array<int,7> perm{0,1,2,3,4,5,6};int ip=0;int best=0;cerr<<"slice_count "<<hs.size()<<" sizes "<<hs.front().v.size()<<" "<<hs.back().v.size()<<endl;
 do{if(ip++%permStride)continue;for(int x=1;x<128;x++)baseMap[x]=baseMap[x&(x-1)]|(1<<perm[countr_zero(unsigned(x))]);
 for(int j=0;j<hs.size();j++){auto&b=hs[j];M occ=0,sat=0;for(int x:b.v){occ|=M(1)<<baseMap[x];if(bit(b.sat,x))sat|=M(1)<<baseMap[x];}
 for(int t=0;t<128;t++){M sx=shift(occ,t),sd=shift(sat,t);for(int i=0;i<=j;i++){auto&a=hs[i];if(!a.purpose&&!b.purpose)continue;int n=a.v.size()+b.v.size();if(n<minN)break;int need=n-2-a.edges-b.edges;if(need<0||need>min(a.ends,b.ends))continue;
 ++tests;if((a.occ&sd)||(a.sat&sx))continue;if(weight(a.occ&sx)!=need)continue;++filtered;emit(a.occ,sx);}
 }}
 }while(next_permutation(perm.begin(),perm.end()));cerr<<"placements "<<tests<<" aggregate_ok "<<filtered<<" raw_paths "<<validN<<" distinct "<<uniqueKeys.size()<<" best "<<maxN<<endl;
}
