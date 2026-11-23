#include <array>
#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <map>
#include <vector>
using namespace std;
uint64_t mix(uint64_t x){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;return x^(x>>31);}
int main(int argc,char**){string line;map<string,int> ids;int fresh=0;while(getline(cin,line)){istringstream f(line);int r,m,b,n,y;f>>r>>m>>b>>n;vector<int>p;while(f>>y)p.push_back(y);int id=fresh++;
 array<int,512>w{};for(int i=0;i<n;i++)for(int j=0;j<i;j++)w[p[i]^p[j]]++;array<uint64_t,512>h{};
 for(int x:p)for(int y:p)if(x!=y)h[x]+=mix(1+w[x^y]);
 vector<int> ord=p;sort(ord.begin(),ord.end(),[&](int a,int b){return pair(h[a],a)<pair(h[b],b);});
 int start=ord[0];vector<int> chosen;array<int,512>co;co.fill(-1);co[0]=0;vector<int>span{0};for(int x:ord){int g=x^start;if(co[g]>=0)continue;chosen.push_back(g);int old=span.size();for(int j=0;j<old;j++){int v=span[j]^g;co[v]=old+j;span.push_back(v);}if(span.size()==512)break;}
 bitset<512>bits;for(int x:p)bits.set(co[x^start]);string repr=bits.to_string();auto [it,inserted]=ids.emplace(repr,id);cout<<r<<" "<<m<<" "<<b<<" "<<n<<" "<<it->second;if(argc>1){cout<<" "<<start;for(int q:chosen)cout<<" "<<q;}cout<<endl;
}}
