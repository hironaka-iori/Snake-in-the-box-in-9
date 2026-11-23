// Leave a contiguous gap in an upper Q8 snake, and anchor its two components to a lower Q8 snake.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;using U=uint64_t;using Mask=array<U,4>;using P=vector<int>;using Perm=array<unsigned char,256>;
vector<P> library(const string&name){ifstream in(name);vector<P>a;string w;while(in>>w){P p{0};for(char c:w){if(c<'0'||c>'7')abort();p.push_back(p.back()^1<<(c-'0'));}
 for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||(popcount((unsigned)(p[i]^p[j]))==1)!=(j+1==i))abort();a.push_back(p);}if(a.empty())abort();return a;}
Perm canonical(int delta){array<int,8>rank;int lo=0,hi=popcount((unsigned)delta);for(int i=0;i<8;i++)rank[i]=((delta>>i)&1)?lo++:hi++;
 Perm m{};for(int x=1;x<256;x++)m[x]=m[x&(x-1)]^(1<<rank[countr_zero((unsigned)x)]);return m;}
vector<Perm>stabilizer(int s){array<int,8>a;iota(a.begin(),a.end(),0);vector<Perm>res;do{
 bool ok=true;for(int j=0;j<8;j++)if((j<s)!=(a[j]<s)){ok=false;break;}if(!ok)continue;
 Perm m{};for(int x=1;x<256;x++)m[x]=m[x&(x-1)]^(1<<a[countr_zero((unsigned)x)]);res.push_back(m);
 }while(next_permutation(a.begin(),a.end()));return res;}
void setbit(Mask&m,int x){m[x/64]|=1ULL<<(x%64);}
bool has(const Mask&m,int x){return m[x/64]>>(x%64)&1;}
struct Block{array<U,256>at{};};
int main(int argc,char**argv){
 if(argc!=8)return 2;int goal=stoi(argv[3]),la=stoi(argv[4]),distance=stoi(argv[5]),start=stoi(argv[6]),stop=stoi(argv[7]),Usize=goal-la;
 auto lower=library(argv[1]),upper=library(argv[2]);set<Mask>right;
 array<Perm,256> maps;for(int j=0;j<256;j++)maps[j]=canonical(j);const int endpoint=(1<<distance)-1;
 for(auto &b:upper){int hole=(int)b.size()-Usize;if(hole<1)continue;
  for(int k=1;k+hole<(int)b.size();k++){for(int x:{0,k-1})for(int y:{k+hole,(int)b.size()-1}){
    int delta=b[x]^b[y];if(popcount((unsigned)delta)!=distance)continue;auto &m=maps[delta];Mask mask{};
    for(int i=0;i<(int)b.size();i++)if(i<k||i>=k+hole)setbit(mask,m[b[i]^b[x]]);
    right.insert(mask);
  }}
 }
 vector<Mask>rs(right.begin(),right.end());if(rs.empty()){cout<<"EMPTY"<<endl;return 0;}
 // Put similar rooted forests in the same 64-element block for early elimination.
 vector<Block>blocks((rs.size()+63)/64);for(int i=0;i<(int)rs.size();i++)for(int x=0;x<256;x++)if(has(rs[i],x))blocks[i/64].at[x]|=1ULL<<(i%64);
 array<int,256>freq{};for(auto&b:blocks)for(int v=0;v<256;v++)freq[v]+=popcount(b.at[v]);
 auto perms=stabilizer(distance);int completed=0;long long trials=0,tests=0;
 cout<<"INIT "<<rs.size()<<" rooted_forests "<<perms.size()<<" permutations "<<lower.size()<<" candidate_mothers"<<endl;
for(int ix=start;ix<(int)lower.size()&&(!stop||ix<stop);ix++){auto a=lower[ix];if((int)a.size()!=la+1||popcount((unsigned)(a.front()^a.back()))!=distance)continue;
 for(int dir=0;dir<2;dir++,reverse(a.begin(),a.end())){P normalized;for(int x:a)normalized.push_back(maps[a.front()^a.back()][x^a.front()]);
  for(auto &perm:perms){P r;for(int x:normalized)r.push_back(perm[x]);P interior(r.begin()+1,r.end()-1);sort(interior.begin(),interior.end(),[&](int x,int y){return freq[x]>freq[y];});trials++;
   for(int k=0;k<(int)blocks.size();k++){U remain=~U(0);if(k+1==(int)blocks.size()&&rs.size()%64)remain=(1ULL<<(rs.size()%64))-1;
    auto&b=blocks[k];for(int v:interior){remain&=~b.at[v];if(!remain)break;}tests++;
    if(!remain)continue;auto mask=rs[k*64+countr_zero(remain)];P joined;
    for(int root:{0,endpoint}){P arm;int prev=-1,v=root;while(v>=0){arm.push_back(v+256);int next=-1;for(int d=0;d<8;d++){int z=v^1<<d;if(z!=prev&&has(mask,z)){if(next>=0)abort();next=z;}}prev=v;v=next;}
     if(!root){joined.assign(arm.rbegin(),arm.rend());joined.insert(joined.end(),r.begin(),r.end());}else joined.insert(joined.end(),arm.begin(),arm.end());}
    if((int)joined.size()!=goal+1)abort();for(int i=0;i<(int)joined.size();i++)for(int j=0;j<i;j++)if(joined[i]==joined[j]||(popcount((unsigned)(joined[i]^joined[j]))==1)!=(j+1==i))abort();
    cout<<"FOUND "<<goal<<" vertices";for(int v:joined)cout<<" "<<v;cout<<endl;return 0;
   }
  }}completed++;if(completed%60==0)cout<<"progress "<<completed<<" trials "<<trials<<" blocks "<<tests<<endl;
 }cout<<"DONE "<<completed<<" trials "<<trials<<" blocks "<<tests<<endl;
}
