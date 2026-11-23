#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;
int main(int argc,char**argv){
 if(argc!=4)return 2;int mink=stoi(argv[1]),minksum=stoi(argv[2]),limit=stoi(argv[3]),nrec=0;long long ncases=0;array<int,9>best{};set<P>seen;
 string line;while(getline(cin,line)){istringstream in(line);int n,x;if(!(in>>n))continue;P p{0};while(in>>x)p.push_back(p.back()^1<<x);if(n<10||n>13)return 3;
 for(int mask=0;mask<(1<<n);mask++)if(popcount((unsigned)mask)==9){
  int bit[13],a=1,b=512;for(int j=0;j<n;j++)if(mask>>j&1){bit[j]=a;a*=2;}else{bit[j]=b;b*=2;}
  P m(1<<n);for(int j=1;j<(1<<n);j++)m[j]=m[j&(j-1)]|bit[countr_zero((unsigned)j)];
  vector<vector<P>> s(1<<(n-9));int prev=-1;for(int v:p){int t=m[v];if((t>>9)!=prev){prev=t>>9;s[prev].emplace_back();}s[prev].back().push_back(t&511);}
  for(auto&parts:s){if(parts.empty())continue;ncases++;sort(parts.begin(),parts.end(),[](auto&a,auto&b){return a.size()>b.size();});int total=0;P key;
   for(int k=0;k<(int)parts.size()&&k<8;k++){total+=parts[k].size();best[k+1]=max(best[k+1],total);}
   total=0;for(int j=0;j<min(mink,(int)parts.size());j++)total+=parts[j].size();if(total<minksum)continue;
   for(int j=0;j<min(mink,(int)parts.size());j++){auto q=parts[j];key.push_back(q.size());key.insert(key.end(),q.begin(),q.end());}
   if(seen.insert(key).second){for(int v:key)cout<<v<<" ";cout<<"\n";}
  }
 }if(++nrec==limit)break;}
 cerr<<"donor "<<nrec<<" facets "<<ncases<<" best_by_components";for(int k=1;k<9;k++)cerr<<" "<<best[k];cerr<<" rows "<<seen.size()<<endl;}

