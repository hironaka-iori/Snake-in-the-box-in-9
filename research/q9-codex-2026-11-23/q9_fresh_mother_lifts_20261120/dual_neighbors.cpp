#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;using Mask=array<uint64_t,4>;using Perm=array<int,8>;
struct Shape{string w;vector<int>p{0};Mask m{};Shape(string s):w(s){for(char c:w)p.push_back(p.back()^(1<<(c-'0')));for(int v:p)m[v>>6]|=1ULL<<(v%64);}};struct Target:Shape{int best=200,id=-1,rev=0;Perm per{};using Shape::Shape;};
int main(int n,char**argv){
 ifstream chart(argv[1]);string w;vector<Shape> seeds;while(chart>>w)seeds.emplace_back(w);array<vector<Target>,256> bins;
 while(cin>>w){Target t(w);bins[t.p.back()].push_back(std::move(t));}
 for(int j=0;j<seeds.size();j++){auto&s=seeds[j];Perm a;iota(a.begin(),a.end(),0);do{
 int f[256]{};for(int x=1;x<256;x++)f[x]=f[x&(x-1)]^(1<<a[countr_zero(unsigned(x))]);int edge=f[s.p.back()];auto&bin=bins[edge];if(bin.empty())continue;
 for(int rev=0;rev<2;rev++){Mask m{};int t=rev*edge;for(int v:s.p){int x=f[v]^t;m[x>>6]|=1ULL<<(x%64);}
 for(auto&c:bin){int diff=0;for(int k=0;k<4;k++){diff+=popcount(m[k]&~c.m[k]);if(diff>=c.best)break;}if(diff<c.best){c.best=diff;c.id=j;c.rev=rev;c.per=a;}}
 }
 }while(next_permutation(a.begin(),a.end()));}
 for(auto&bin:bins)for(auto&t:bin){cout<<t.best<<" "<<t.id<<" "<<t.rev<<" ";for(int k:t.per)cout<<k;cout<<" "<<t.w<<'\n';}
}
