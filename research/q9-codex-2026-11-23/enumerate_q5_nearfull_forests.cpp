#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <vector>
using namespace std;using U=uint32_t;using P=vector<int>;
U nb[32];int pc(U m){return __builtin_popcount(m);}
bool forest(U m,int d){
 U todo=m;while(todo){U c=todo&-todo,fr=c;int sum=0;
  while(fr){U nx=0;for(U q=fr;q;q&=q-1){int v=__builtin_ctz(q);U n=nb[v]&m;
   if(pc(n)>2)return false;sum+=pc(n);nx|=n;}fr=nx&~c;c|=fr;}
  if(sum/2!=pc(c)-1)return false;todo&=~c;
 }return true;
}
struct Slice{U mask,d0,d1,d2;int comps;};
int main(int argc, char** argv){
 if(argc!=2)return 2;int target=stoi(argv[1]);if(target!=15 && target!=16)return 2;
 for(int x=0;x<32;x++)for(int d=0;d<5;d++)nb[x]|=1u<<(x^(1<<d));
 vector<U> halves;int mx=0;
 for(U v=0;v<1u<<16;v++)if(forest(v,4)){mx=max(mx,pc(v));if(pc(v)==7||pc(v)==8)halves.push_back(v);}
 cerr<<"Q4 max "<<mx<<" optimal "<<halves.size()<<endl;
 assert(mx==8);vector<Slice> pits;map<int,long long> cs;
 for(U a:halves)for(U b:halves){if(pc(a)+pc(b)!=target)continue;U x=a|(b<<16);if(!forest(x,5))continue;U m[3]{};
  for(U q=x;q;q&=q-1){int v=__builtin_ctz(q);m[pc(nb[v]&x)]|=1u<<v;}
  int k=pc(m[0])+pc(m[1])/2;cs[k]++;pits.push_back({x,m[0],m[1],m[2],k});
 }cerr<<"Q5 bank "<<pits.size()<<endl;for(auto z:cs)cerr<<z.first<<":"<<z.second<<" ";cerr<<endl;
 for(auto &s:pits)cout<<s.mask<<" "<<s.d0<<" "<<s.d1<<" "<<s.d2<<" "<<s.comps<<"\n";
}
