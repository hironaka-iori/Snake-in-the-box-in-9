#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>
using namespace std;using M=array<uint64_t,4>;using P=vector<int>;using T=chrono::steady_clock;
M operator&(M a,M b){for(int i=0;i<4;i++)a[i]&=b[i];return a;}M operator|(M a,M b){for(int i=0;i<4;i++)a[i]|=b[i];return a;}M operator^(M a,M b){for(int i=0;i<4;i++)a[i]^=b[i];return a;}M diff(M a,M b){for(int i=0;i<4;i++)a[i]&=~b[i];return a;}int sizeM(M a){int n=0;for(auto w:a)n+=popcount(w);return n;}bool has(M a,int x){return a[x>>6]>>(x&63)&1;}void put(M&a,int x){a[x>>6]|=1ull<<(x&63);}
uint64_t mix(uint64_t z){z+=0x9e3779b97f4a7c15ull;z=(z^(z>>30))*0xbf58476d1ce4e5b9ull;z=(z^(z>>27))*0x94d049bb133111ebull;return z^(z>>31);}
struct Parent{int id,ori,d;M S{},upper{},lower{};array<array<short,2>,256> adj;P q;Parent(){for(auto &x:adj)x={-1,-1};}};
struct Face{int mask,value;M bits{};P points;};struct Port{uint64_t exact=0,approx=0;P e;};vector<Parent> bank;set<M> originals,seen;M odd{};mt19937 rng;long long pairs=0,tried=0,rejected=0,saved=0,ham=0,exact=0;int target,perface,globalCap;
bool hamiltonian(int a,int b,Face const&f,Port const&pa,Port const&pb,M s){if(pa.e!=pb.e)return false;int degree[256]{},next[256][2];for(int x=0;x<256;x++)if(has(s,x)){
 bool in=has(f.bits,x);auto&p=(in?bank[b]:bank[a]);for(int y:p.adj[x])if(y>=0){if(!has(s,y))return false;next[x][degree[x]++]=y;}}
 int ends=0,root=-1;for(int x=0;x<256;x++)if(has(s,x)){if(!degree[x])return false;if(degree[x]==1){ends++;root=x;}}if(ends!=2)return false;
 int last=-1,n=0;for(int x=root;x>=0;){int nx=-1;for(int j=0;j<degree[x];j++)if(next[x][j]!=last)nx=next[x][j];n++;last=x;x=nx;if(n>256)return false;}return n==sizeM(s);}
int save(int a,int b,Face const&f,Port const&pa,Port const&pb,bool approx){++pairs;
 auto&A=bank[a];auto&B=bank[b];if(A.id==B.id||A.S==B.S)return 0;
 M added=diff(B.S,A.S)&f.bits,removed=diff(A.S,B.S)&f.bits;if(!sizeM(added)||!sizeM(removed))return 0;
 M s=diff(A.S,f.bits)|(B.S&f.bits);if(originals.count(s)||seen.count(s))return 0;
 int n=sizeM(s),parity=sizeM(s&odd);if(abs(2*parity-n)>1||n>target+1)return 0;
 int sym=0;for(int edge:pa.e)if(!binary_search(pb.e.begin(),pb.e.end(),edge))sym++;for(int edge:pb.e)if(!binary_search(pa.e.begin(),pa.e.end(),edge))sym++;
 if(sym>12)return 0;tried++;int d1=0,free=0;for(int x=0;x<256;x++)if(has(s,x)){int k=0;for(int d=0;d<8;d++)k+=has(s,x^(1<<d));if(!k)return 0;if(k==1)d1++;if(k<=2)free++;}
 if(d1>2||free<target+1-n){rejected++;return 0;}bool h=hamiltonian(a,b,f,pa,pb,s);if(!sym)exact++;if(h)ham++;
 seen.insert(s);cout<<a<<" "<<b<<" "<<f.mask<<" "<<f.value<<" "<<sizeM(added)<<" "<<sizeM(removed)<<" "<<sym<<" "<<h<<" "<<n<<" "<<free<<endl;saved++;return 1;
}
int main(int argc,char**argv){if(argc!=6)return 1;target=atoi(argv[1]);perface=atoi(argv[2]);globalCap=atoi(argv[3]);int sec=atoi(argv[4]);rng.seed(strtoul(argv[5],nullptr,10));
 for(int x=0;x<256;x++)if(popcount(unsigned(x))%2)put(odd,x);string line;while(getline(cin,line)){istringstream in(line);Parent p;in>>p.id>>p.ori>>p.d;int x;while(in>>x){int v=x%256;put(p.S,v);put(x>=256?p.upper:p.lower,v);if(p.q.empty()||p.q.back()!=v)p.q.push_back(v);}if(sizeM(p.S)!=p.q.size())abort();for(int i=0;i<p.q.size();i++)p.adj[p.q[i]]={short(i?p.q[i-1]:-1),short(i+1<p.q.size()?p.q[i+1]:-1)};originals.insert(p.S);bank.push_back(move(p));}
 vector<Face>faces;for(int m=1;m<256;m++){int k=popcount(unsigned(m));if(k<2||k>5)continue;for(int v=m;;v=(v-1)&m){Face f{m,v};for(int x=0;x<256;x++)if((x&m)==v){f.points.push_back(x);put(f.bits,x);}faces.push_back(f);if(!v)break;}}
 shuffle(faces.begin(),faces.end(),rng);vector<int> order(bank.size());iota(order.begin(),order.end(),0);auto start=T::now();int fct=0;
 for(auto&f:faces){++fct;shuffle(order.begin(),order.end(),rng);unordered_map<uint64_t,P>exactBins,weakBins;vector<Port> ports(bank.size());int local=0;
 for(int i:order){auto&p=bank[i];auto&port=ports[i];for(int x:f.points)if(has(p.S,x))for(int y:p.adj[x])if(y>=0&&!has(f.bits,y)){int e=x*256+y;uint64_t z=mix(e);port.e.push_back(e);port.exact^=z;if((z&3)==0)port.approx^=z;}sort(port.e.begin(),port.e.end());
 auto exercise=[&](P&v,bool approx){if(!v.empty()){
 int off=rng()%v.size(),cnt=min(int(v.size()),approx?6:12);for(int k=0;k<cnt;k++){int j=v[(off+k)%v.size()];local+=save(i,j,f,port,ports[j],approx);local+=save(j,i,f,ports[j],port,approx);if(local>=perface)return;}}
 if(v.size()<70)v.push_back(i);else if(rng()%3==0)v[rng()%v.size()]=i;};
 exercise(exactBins[port.exact],false);if(local<perface)exercise(weakBins[port.approx],true);
 if(local>=perface||saved>=globalCap)break;
 }if(saved>=globalCap||chrono::duration<double>(T::now()-start).count()>=sec)break;}
 cerr<<"parents "<<bank.size()<<" distinct_source_sets "<<originals.size()<<" faces "<<fct<<" pairs "<<pairs<<" prefiltered "<<tried<<" size_or_leaf_reject "<<rejected<<" saved "<<saved<<" exact_ports "<<exact<<" projected_hamiltonian "<<ham<<endl;}

