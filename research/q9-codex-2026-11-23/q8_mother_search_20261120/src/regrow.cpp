#include<algorithm>
#include<array>
#include<cassert>
#include<fstream>
#include<iostream>
#include<set>
#include<random>
#include<string>
#include<vector>
using namespace std;using P=vector<int>;mt19937 rng(711123);
string norm(const P&p,bool rev){int r[8];fill(r,r+8,-1);int cnt=0;string w;for(int k=1;k<p.size();k++){int i=rev?p.size()-k:k;int x=__builtin_ctz(p[i]^p[i-1]);if(r[x]<0)r[x]=cnt++;w+='0'+r[x];}return w;}
string can(const P&p){return min(norm(p,0),norm(p,1));}
bool verify(const P&p){for(int j=1;j<p.size();j++)for(int i=0;i<j;i++){int d=__builtin_popcount(unsigned(p[i]^p[j]));if(!d||((d==1)!=(j==i+1)))return false;}return true;}
int main(int argc,char**argv){int jobs=stoi(argv[2]),budget=stoi(argv[3]);vector<P> parents;set<string>seen;
 auto read=[&](istream&in){string w;while(in>>w)if(w.size()>=96){P p{0};for(char c:w)p.push_back(p.back()^1<<(c-'0'));if(seen.insert(can(p)).second)parents.push_back(p);}};read(cin);ifstream n(argv[1]);read(n);
 long long nodes=0;int news[99]{},starts=parents.size();int d[256][8];
 for(int t=0;t<jobs;t++){P p=parents[rng()%parents.size()];if(rng()%2)reverse(p.begin(),p.end());int k=2+rng()%45;
  p.resize(p.size()-k);auto parent=p;unsigned char hit[256]{};
  auto add=[&](int v,int sign){hit[v]+=sign;for(int h=0;h<8;h++)hit[v^1<<h]+=sign;};
  for(int i=0;i+1<p.size();i++)add(p[i],1);
  for(auto&row:d){iota(row,row+8,0);shuffle(row,row+8,rng);}
  int ticks=0;
  auto dfs=[&](auto&&self)->void{int v=p.back();ticks++;if(p.size()>=97){auto key=can(p);if(seen.insert(key).second){assert(verify(p));news[p.size()-1]++;
     parents.push_back(p);cout<<norm(p,false)<<" "<<t<<" "<<k<<" "<<can(parent)<<endl;}if(p.size()==99)return;}
    int cand[8],nc=0;for(int h:d[v]){int w=v^1<<h;if(!hit[w])cand[nc++]=w;}
    add(v,1);for(int i=0;i<nc&&ticks<budget;i++){p.push_back(cand[i]);self(self);p.pop_back();}add(v,-1);
  };dfs(dfs);nodes+=ticks;
 }cerr<<"start "<<starts<<" jobs "<<jobs<<" nodes "<<nodes<<" fresh 96 97 98 "<<news[96]<<" "<<news[97]<<" "<<news[98]<<endl;}
