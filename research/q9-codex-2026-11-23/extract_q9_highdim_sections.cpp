// Export dense nine-dimensional sections, retaining every path component.
#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
int main(){string l;set<array<unsigned long long,8>> seen;map<int,int> count;
 while(getline(cin,l)){istringstream in(l);int n,x;in>>n;vector<int> p;while(in>>x)p.push_back(x);
 for(int m=0;m<(1<<n);m++)if(__builtin_popcount(unsigned(m))==9){
 array<int,13> mask{};int j=0,k=0;for(int d=0;d<n;d++)mask[d]=m&(1<<d)?1<<j++:1<<(9+k++);
 vector<int> lookup(1<<n);for(int i=1;i<(1<<n);i++)lookup[i]=lookup[i&(i-1)]|mask[__builtin_ctz(unsigned(i))];
 vector<vector<int>> cells(1<<(n-9));vector<int> runs(1<<(n-9));int last=-1;
 for(int u:p){int v=lookup[u];cells[v>>9].push_back(v&511);if((v>>9)!=last){last=v>>9;runs[last]++;}}
 for(size_t z=0;z<cells.size();z++){auto &f=cells[z];if(f.size()<183||runs[z]>18)continue;
 array<unsigned long long,8> key{};for(int v:f)key[v/64]|=1ull<<(v%64);
 if(!seen.insert(key).second)continue;
 cout<<n<<" "<<runs[z]<<" "<<f.size();for(int v:f)cout<<" "<<v;cout<<"\n";count[n]++;
 }
 }}
 for(auto [n,c]:count)cerr<<"Q"<<n<<" "<<c<<endl;
}
