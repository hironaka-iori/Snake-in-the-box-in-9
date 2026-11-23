#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
using P=vector<int>;using Pair=array<P,2>;using Mask=array<uint64_t,4>;
unsigned char deg[256],on[256];int nb[256][8],target,cut,mindonor,sec,all=0,best=0;long long cores=0,visits=0,raw=0;bool stopped=false;chrono::steady_clock::time_point start;
set<Mask> seen;
void setv(int x,int sign){on[x]=sign>0;for(int y:nb[x])deg[y]+=sign;}
Pair base;array<P,4> endGrafts;
void emit(){Mask m{};for(int i=0;i<256;i++)if(on[i])m[i/64]|=1ull<<(i%64);if(!seen.insert(m).second)return;Pair out=base;
 for(int j=0;j<2;j++){auto&a=out[j];auto&l=endGrafts[2*j];a.insert(a.begin(),l.rbegin(),l.rend());auto&r=endGrafts[2*j+1];a.insert(a.end(),r.begin(),r.end());}int minl=min(out[0].size(),out[1].size());
 int n=out[0].size()+out[1].size();if(n>best){best=n;cerr<<"best "<<n<<" core "<<cores<<" visited "<<visits<<endl;}++raw;if(raw>30000&&n<=100)return;
 int off=out[0][0];for(auto&a:out){cout<<a.size();for(int x:a)cout<<" "<<(x^off);cout<<" ";}cout<<endl;}
void grow(int pos,int x,int vertices){if(stopped)return;++visits;if((visits&1048575)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=sec){stopped=true;return;}
 if(vertices>=target)emit();if(vertices>=max(target+2,102))return;
 if(pos<3){auto&a=base[(pos+1)/2];int next=(pos+1)%2?a.back():a.front();grow(pos+1,next,vertices);}
 // The only chosen neighbour must be the current endpoint. Its existing degree may be one or zero.
 if(deg[x]>=2)return;
 for(int y:nb[x])if(!on[y]&&deg[y]==1){setv(y,1);endGrafts[pos].push_back(y);grow(pos,y,vertices+1);endGrafts[pos].pop_back();setv(y,-1);}
}
bool timed(){return chrono::duration<double>(chrono::steady_clock::now()-start).count()>=sec;}
int main(int argc,char**argv){if(argc!=5)return 1;target=atoi(argv[1]);cut=atoi(argv[2]);mindonor=atoi(argv[3]);sec=atoi(argv[4]);start=chrono::steady_clock::now();for(int x=0;x<256;x++)for(int d=0;d<8;d++)nb[x][d]=x^(1<<d);
 vector<Pair> donors;string s;while(getline(cin,s)){istringstream in(s);Pair a;int n,x;for(int j=0;j<2;j++){if(!(in>>n))return 2;for(int i=0;i<n;i++){in>>x;a[j].push_back(x);}}if(in>>n)return 3;if(a[0].size()+a[1].size()>=mindonor)donors.push_back(a);}
 // Visit breadth by total cut for equitable use of all donors.
 for(int k=0;k<=cut&&!stopped;k++)for(auto&orig:donors){int n=orig[0].size()+orig[1].size();for(int a=0;a<=k&&!stopped;a++)for(int b=0;a+b<=k&&!stopped;b++)for(int c=0;a+b+c<=k&&!stopped;c++){
 int d=k-a-b-c;if(a+b>=orig[0].size()||c+d>=orig[1].size())continue;
 base[0]={orig[0].begin()+a,orig[0].end()-b};base[1]={orig[1].begin()+c,orig[1].end()-d};
 for(auto&p:base)for(int v:p)setv(v,1);++cores;grow(0,base[0].front(),n-k);for(auto&p:base)for(int v:p)setv(v,-1);if((cores&4095)==0&&timed())stopped=true;
 }}cerr<<"donors "<<donors.size()<<" cores "<<cores<<" nodes "<<visits<<" unique "<<raw<<" max "<<best<<" cutoff "<<stopped<<endl;
}
