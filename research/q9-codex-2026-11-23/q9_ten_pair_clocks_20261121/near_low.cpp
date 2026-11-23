#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
string canon(string s){
  auto norm=[](string w){array<char,5> seen={};char next='0';for(auto& c:w){if(c=='4')continue;int idx=c-'0';if(!seen[idx])seen[idx]=next++;c=seen[idx];}return w;};
  string a=norm(s);reverse(s.begin(),s.end());return min(a,norm(s));
}
int main(){
  ifstream inp("../q9_two_sheet_chart_20261121/near_573291.pts");
  vector<array<int,1024>> counts;
  for(string line;getline(inp,line);){
    istringstream ss(line);int dim,x;ss>>dim;vector<int> p;
    while(ss>>x)p.push_back(x);array<int,1024> h={};
    for(int j=0;j<p.size();j++)for(int i=0;i+1<j;i++)h[p[i]^p[j]]++;
    counts.push_back(h);
  }
  ifstream ranges("near192.ranges");ofstream out("near_low.tsv");
  set<string> keys;map<int,long> selected,unique;
  for(string line;getline(ranges,line);){
    istringstream ss(line);int r,l;string axes,w,st;ss>>r>>l>>axes>>w>>st;int mask=0;
    for(int i=0;i<10;i++)if(axes[i]=='8')mask|=1<<i;
    int cost=counts[r][mask];
    for(int i=0;i<10;i++)if(!(mask>>i&1))cost+=counts[r][mask^(1<<i)];
    // Neighbours due to a single source-axis flip cannot occur nonconsecutively
    // because the original Q10 path is induced.
    if(cost>2)continue;selected[cost]++;
    string g=w;for(auto& c:g)c='0'+(c-'0')/2;
    if(keys.insert(canon(g)).second){unique[cost]++;out<<r<<" 0 "<<l<<" "<<axes<<" "<<cost<<" "<<g<<" "<<w<<"\n";}
  }
  for(auto [cost,n]:selected)cout<<cost<<" "<<n<<" "<<unique[cost]<<"\n";
}
