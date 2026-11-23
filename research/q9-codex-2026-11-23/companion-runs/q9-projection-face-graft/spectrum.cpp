#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using V=array<int16_t,256>;using P=array<uint64_t,4>;
V signature(P p){V f{},out{};for(int x=0;x<256;x++)f[x]=(p[x>>6]>>(x&63))&1;
 for(int h=1;h<256;h*=2)for(int k=0;k<256;k+=2*h)for(int j=0;j<h;j++){int a=f[k+j],b=f[k+j+h];f[k+j]=a+b;f[k+j+h]=a-b;}
 int pos=0;for(int d=0;d<=8;d++){int a=pos;for(int x=0;x<256;x++)if(popcount(unsigned(x))==d)out[pos++]=abs(f[x]);sort(out.begin()+a,out.begin()+pos);}return out;}
int main(int argc,char**argv){if(argc<3)return 1;ifstream in(argv[1]);vector<P> parents;set<P> orig;string l;while(getline(in,l)){istringstream s(l);int id,o,d,z;s>>id>>o>>d;P p{};while(s>>z){z&=255;p[z>>6]|=1ull<<(z&63);}parents.push_back(p);orig.insert(p);}
 set<V> pub,all;for(auto&p:orig)pub.insert(signature(p));long long outputs=0,novel=0;map<V,int>unique;for(int j=2;j<argc;j++){ifstream g(argv[j]);string line;while(getline(g,line)){istringstream s(line);int a,b,m,v;if(!(s>>a>>b>>m>>v))continue;P p=parents[a];for(int x=v;x<256;x++)if((x&m)==v){int i=x>>6;uint64_t b0=1ull<<(x&63);p[i]=(p[i]&~b0)|(parents[b][i]&b0);}V f=signature(p);outputs++;all.insert(f);if(!pub.count(f)){novel++;unique.try_emplace(f,0);}}}
 cout<<"source_raw "<<orig.size()<<" source_invariants "<<pub.size()<<" outputs "<<outputs<<" output_invariants "<<all.size()<<" no_source_signature "<<novel<<" distinct_absent_signatures "<<unique.size()<<endl;}

