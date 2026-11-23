// Collect genuine two-component Q8 forests by slicing public higher-dimensional snakes.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using P=vector<int>;
int main(int argc,char**argv){
 if(argc!=3)return 2;int minimum=stoi(argv[1]),limit=stoi(argv[2]);string l;set<vector<int>>seen;
 long long cuts=0,pairs=0;int entries=0;
 while(getline(cin,l)){istringstream in(l);int n,x;if(!(in>>n))continue;if(n<9||n>13)abort();P p{0};while(in>>x){if(x<0||x>=n)abort();p.push_back(p.back()^1<<x);}
 for(int mask=0;mask<(1<<n);mask++){if(popcount((unsigned)mask)!=8)continue;cuts++;
  vector<int>trans(1<<n);int ax[13]={},weight=1;for(int i=0;i<n;i++)if(mask>>i&1){ax[i]=weight;weight*=2;}
  for(int i=1;i<(1<<n);i++)trans[i]=trans[i&(i-1)]|ax[countr_zero((unsigned)i)];
  vector<vector<pair<int,int>>> runs(1<<(n-8));auto outer=[&](int v){int b=0;for(int i=0;i<n;i++)if(!(mask>>i&1))b=2*b+(v>>i&1);return b;};
  for(int j=0;j<(int)p.size();){int k=j+1;while(k<(int)p.size()&&((p[k]^p[j])&~mask)==0)k++;runs[outer(p[j])].push_back({j,k});j=k;}
  for(auto&group:runs){sort(group.begin(),group.end(),[](auto a,auto b){return a.second-a.first>b.second-b.first;});
   for(int i=1;i<(int)group.size()&&group[0].second-group[0].first+group[i].second-group[i].first>=minimum;i++)
    for(int j=0;j<i;j++){auto[a,b]=group[j];auto[c,d]=group[i];if(b-a+d-c<minimum)break;
     P A,B;for(int h=a;h<b;h++)A.push_back(trans[p[h]]);for(int h=c;h<d;h++)B.push_back(trans[p[h]]);pairs++;
     if(A.back()<A.front())reverse(A.begin(),A.end());if(B.back()<B.front())reverse(B.begin(),B.end());
     int origin=A[0];vector<int>key{(int)A.size()};for(int v:A)key.push_back(v^origin);key.push_back(B.size());for(int v:B)key.push_back(v^origin);if(seen.insert(key).second){for(int z:key)cout<<z<<" ";cout<<"\n";}
   }
  }
 }
 if(++entries==limit)break;
 }
 cerr<<entries<<" donors "<<cuts<<" facets "<<pairs<<" admissible pairs "<<seen.size()<<" coordinate lists"<<endl;
}
