#include <algorithm>
#include <array>
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <cassert>
using namespace std;struct Arm{string w;vector<int>p;array<uint64_t,4> m{};};
int main(int argc,char**argv){vector<Arm> arms,newarms;string w;auto read=[&](istream& in,vector<Arm>&out){while(in>>w){Arm a;a.w=w;int x=0;for(char d:w){x^=1<<(d-'0');a.p.push_back(x);a.m[x>>6]|=1ull<<(x&63);}out.push_back(a);}sort(out.begin(),out.end(),[](auto&a,auto&b){return a.w.size()>b.w.size();});};ifstream st(argv[1]);read(st,newarms);read(cin,arms);arms.insert(arms.end(),newarms.begin(),newarms.end());sort(arms.begin(),arms.end(),[](auto&a,auto&b){return a.w.size()>b.w.size();});
 array<int,8> perm{0,1,2,3,4,5,6,7};array<uint64_t,199> tries{},hits{};int ct=0;
 do{int image[256]{};for(int i=1;i<256;i++)image[i]=image[i&(i-1)]^1<<perm[__builtin_ctz(i)];
 for(auto& a:newarms){if(a.w.size()+1+arms[0].w.size()<192)continue;array<uint64_t,4> m{};for(int x:a.p){int y=image[x];m[y>>6]|=1ull<<(y&63);}
 for(auto& b:arms){int n=a.w.size()+1+b.w.size();if(n<192)break;tries[n]++;if((m[0]&b.m[0])||(m[1]&b.m[1])||(m[2]&b.m[2])||(m[3]&b.m[3]))continue;
 hits[n]++;if(hits[n]==1){cout<<"WITNESS "<<n;for(auto i=b.p.rbegin();i!=b.p.rend();i++)cout<<" "<<*i;cout<<" 0 256";for(int x:a.p)cout<<" "<<(256+image[x]);cout<<endl;}
 }}ct++;
 }while(next_permutation(perm.begin(),perm.end()));for(int n=192;n<=197;n++)cout<<n<<" ordered_rooted_placements "<<tries[n]<<" hits "<<hits[n]<<endl;
}
