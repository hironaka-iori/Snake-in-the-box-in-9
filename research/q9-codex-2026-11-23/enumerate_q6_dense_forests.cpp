#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>
#include <unordered_set>
using U=uint32_t;using L=uint64_t;
int pc(U v){return __builtin_popcount(v);}
struct Half{U m,d1,d2;int v,e;};
std::vector<Half> inner;
bool forest(L s,int d){
 L rem=s;
 while(rem){
  L fr=rem&-rem;rem^=fr;int vertices=0,twice=0;
  while(fr){L next=0;
   for(L q=fr;q;q&=q-1){int x=__builtin_ctzll(q);vertices++;
    for(int i=0;i<d;i++){L b=L(1)<<(x^(1<<i));twice+=bool(s&b);next|=b;}
   }fr=next&rem;rem^=fr;
  }
  if(twice!=2*(vertices-1))return false;
 }
 return true;
}
Half describe(U m,int d){
 U one=0,two=0;int edges=0;
 for(U s=m;s;s&=s-1){int v=__builtin_ctz(s),k=0;
  for(int j=0;j<d;j++)k+=(m>>(v^(1<<j)))&1;
  if(k>2)return {m,0,0,-1,0};
  if(k==2)two|=U(1)<<v;if(k==1)one|=U(1)<<v;edges+=k;
 }
 return {m,one,two,pc(m),edges/2};
}
std::vector<std::array<U,32>> maps;
void prepare(){
 for(U m=0;m<65536;m++){auto h=describe(m,4);if(h.v>=0 && forest(m,4))inner.push_back(h);}
 std::array<int,5> p={0,1,2,3,4};
 do{for(int t=0;t<32;t++){
  std::array<U,32> tr;
  for(int v=0;v<32;v++){int w=t;for(int i=0;i<5;i++)if(v>>i&1)w^=1<<p[i];tr[v]=U(1)<<w;}maps.push_back(tr);
 }}while(std::next_permutation(p.begin(),p.end()));
}
int main(int argc,char**argv){
 int threshold=argc>1?atoi(argv[1]):28;
 prepare();std::unordered_set<U> seen;int best[33],orbit[17]={}; L witness[33]={};for(int &x:best)x=100;
 for(auto a:inner)for(auto b:inner){
  int na=a.v+b.v;
  if(na<(threshold+1)/2 || a.m&b.d2 || b.m&a.d2)continue;
  U A=a.m|(b.m<<16);if(seen.count(A)||!forest(A,5))continue;
  for(auto &f:maps){U img=0;for(U q=A;q;q&=q-1)img|=f[__builtin_ctz(q)];seen.insert(img);}
  orbit[na]++;
  auto h=describe(A,5);
  std::vector<Half> lo,hi;
  auto filter=[&](std::vector<Half>&list,U am,U banned){
   for(const auto& x:inner)if(x.v>=threshold-na-8 && !(x.m&banned) && !(x.d2&am))list.push_back(x);
  };
  filter(lo,A&65535,h.d2&65535);filter(hi,A>>16,h.d2>>16);
  for(auto l:lo)for(auto r:hi){
   int n=na+l.v+r.v;if(n<threshold||l.v+r.v>na)continue;
   U mid=l.m&r.m;
   if(mid&(l.d2|r.d2|(l.d1&A)|(r.d1&(A>>16))))continue;
   U B=l.m|(r.m<<16);int comp=n-(h.e+l.e+r.e+pc(mid)+pc(A&B));
   if(comp>=best[n] ||comp<=0)continue;
   L all=A|(L(B)<<32);
   if(forest(all,6)){best[n]=comp;witness[n]=all;}
  }
 }
 for(int n=(threshold+1)/2;n<=16;n++)printf("Q5 large half size %d orbit count %d\n",n,orbit[n]);
 for(int n=threshold;n<=32;n++)printf("Q6 vertices %d min_components %d mask %016llx\n",n,best[n],(unsigned long long)witness[n]);
}
