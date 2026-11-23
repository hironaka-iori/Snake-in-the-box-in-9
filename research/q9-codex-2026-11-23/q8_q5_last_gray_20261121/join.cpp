#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using U=uint32_t;
struct R{U m;int tip,n;};
U N[32];
int g[8]={0,1,3,7,5,4,6,2},goal,core;
vector<int> middle[4];
uint64_t tests[4],origins;
void gen(int v,U m,U ban,vector<R>& out,int lo){
 int n=popcount(m);if(n>=lo)out.push_back({m,v,n});
 for(U s=N[v]&~(ban|m);s;s&=s-1){int w=countr_zero(s);gen(w,m|(U(1)<<w),ban|N[v],out,lo);}
}
vector<R> options(int v,U block,int lo){
 vector<R> p;if(!(block&(U(1)<<v)))gen(v,U(1)<<v,block,p,lo);
 sort(p.begin(),p.end(),[](const R&a,const R&b){return a.n>b.n;});return p;
}
vector<int> walk(U m,int v){
 vector<int> p;while(true){p.push_back(v);m^=U(1)<<v;U rem=N[v]&m;if(!rem)break;if(popcount(rem)!=1)abort();v=countr_zero(rem);}if(m)abort();return p;
}
void emit(const R&a,const R&b,const R&c,const R&d,int root,int bstart){
 vector<int> part[8];part[0]=walk(a.m,a.tip);for(int i=0;i<4;i++)part[i+1]=middle[i];
 part[5]=walk(b.m,bstart);part[6]=walk(c.m,b.tip);part[7]=walk(d.m,c.tip);
 vector<int> path;for(int i=0;i<8;i++)for(int x:part[i])path.push_back(32*g[i]+x);
 for(int i=0;i<path.size();i++)for(int j=0;j<i;j++)if(path[i]==path[j]||has_single_bit(unsigned(path[i]^path[j]))!=(j==i-1))abort();
 cout<<"WIT "<<path.size();for(int x:path)cout<<" "<<x;cout<<endl;
}
bool join(const string&w){
 core=w.size()+1;U m[4]{};int k=0,x=0;for(auto &p:middle)p.clear();middle[0]={0};m[0]=1;
 for(char ch:w){int d=ch-'0';if(d>=5){if(++k>3)abort();}else x^=1<<d;middle[k].push_back(x);m[k]|=U(1)<<x;}
 if(k!=3)abort();int bs=x;
 auto as=options(0,m[0]&~U(1),goal-core-39);if(as.empty())return false;
 auto bsopts=options(bs,m[3]&~(U(1)<<bs),goal-core-as[0].n-26);
 for(auto b:bsopts){
  ++tests[0];vector<R> aa;for(auto a:as)if(!(a.m&b.m)&&a.n+b.n+core+26>=goal)aa.push_back(a);
  if(aa.empty())continue;
  auto cs=options(b.tip,m[2]|(b.m&~(U(1)<<b.tip)),goal-core-b.n-aa[0].n-14);
  for(auto c:cs){
   ++tests[1];int rest=goal-core-b.n-c.n;
   auto ds=options(c.tip,m[1]|(c.m&~(U(1)<<c.tip)),rest-aa[0].n);
   for(auto d:ds){++tests[2];for(auto a:aa){if(a.n<rest-d.n)break;++tests[3];if(!(a.m&d.m)){emit(a,b,c,d,0,bs);return true;}}}
  }
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=6)return 2;goal=stoi(argv[2]);int lo=stoi(argv[3]),hi=stoi(argv[4]),limit=stoi(argv[5]);
 for(int v=0;v<32;v++)for(int i=0;i<5;i++)N[v]|=U(1)<<(v^(1<<i));
 ifstream f(argv[1]);if(!f)return 3;vector<string> bank;string w;while(f>>w)if(w.size()+1>=lo&&w.size()+1<=hi)bank.push_back(w);
 stable_sort(bank.begin(),bank.end(),[](auto&a,auto&b){return a.size()>b.size();});
 for(auto&s:bank){if(limit&&origins>=limit)break;++origins;if(join(s)){cout<<"FOUND origin "<<origins<<" "<<s<<endl;return 0;}
  if(origins%2000==0)cout<<"PROGRESS "<<origins<<endl;}
 cout<<"DONE target "<<goal<<" core_range "<<lo<<" "<<hi<<" available "<<bank.size()<<" completed "<<origins<<" nodes";for(auto t:tests)cout<<" "<<t;cout<<endl;
}
