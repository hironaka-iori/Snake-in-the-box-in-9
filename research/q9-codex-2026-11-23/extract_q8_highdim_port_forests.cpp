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
int main(){string l;set<array<unsigned long long,4>> seen;map<int,int> count;
 while(getline(cin,l)){istringstream in(l);int n,x;in>>n;vector<int> p;while(in>>x)p.push_back(x);
 for(int m=0;m<(1<<n);m++)if(__builtin_popcount(unsigned(m))==8){
 array<int,13> mask{};int j=0,k=0;for(int d=0;d<n;d++)mask[d]=m&(1<<d)?1<<j++:1<<(8+k++);
 vector<int> lookup(1<<n);for(int i=1;i<(1<<n);i++)lookup[i]=lookup[i&(i-1)]|mask[__builtin_ctz(unsigned(i))];
 vector<bitset<256>> cells(1<<(n-8));
 for(int u:p){int v=lookup[u];cells[v>>8].set(v&255);}
 for(auto& f:cells){if(f.count()<78||f.count()>115)continue;
 int iso=0,ports=0;array<unsigned long long,4> key{};bool ok=true;
 for(int a=0;a<256;a++)if(f[a]){int d=0;for(int b=0;b<8;b++)d+=f[a^(1<<b)];
 if(d>2)abort();if(!d&&++iso>2){ok=false;break;}ports+=d<2;if(ports>38){ok=false;break;}key[a/64]|=1ull<<(a%64);}
 if(!ok||ports<6||!seen.insert(key).second)continue;
 cout<<"F";for(int i=0;i<256;i++)if(f[i])cout<<" "<<i;cout<<"\n";count[n]++;
 }
 }}
 for(auto [n,c]:count)cerr<<"Q"<<n<<" "<<c<<endl;
}
