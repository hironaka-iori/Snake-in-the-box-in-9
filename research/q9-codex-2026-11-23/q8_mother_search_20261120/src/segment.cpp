#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <set>
#include <random>
using namespace std;
using P=vector<int>;mt19937 rng(342115);
string norm(const P&p,bool rev){array<int,8> l;l.fill(-1);int nxt=0;string w;for(int z=1;z<p.size();z++){int i=rev?p.size()-z:z;int c=__builtin_ctz(p[i]^p[i-1]);if(l[c]<0)l[c]=nxt++;w+='0'+l[c];}return w;}
string can(const P&p){return min(norm(p,false),norm(p,true));}
bool verify(const P&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){int d=__builtin_popcount(unsigned(p[i]^p[j]));if(!d||((d==1)!=(i==j+1)))return false;}return true;}
set<string> seen;vector<P> seeds;long long nodes=0;int nnew[100]{};
int main(int argc,char**argv){string w;while(cin>>w)if(w.size()>=92){P p={0};for(char ch:w)p.push_back(p.back()^(1<<(ch-'0')));if(seen.insert(can(p)).second&&w.size()>=95)seeds.push_back(p);}
 int jobs=stoi(argv[1]),budget=stoi(argv[2]);int start=seeds.size();uniform_int_distribution<int>d8(0,7);
 for(int job=0;job<jobs;job++){P p=seeds[rng()%seeds.size()];if(job%3==0){for(int i=0;i<20&&p.size()<98;i++)p=seeds[rng()%seeds.size()];}
 if(rng()%2)reverse(p.begin(),p.end());int n=p.size(), k=5+rng()%44, a=rng()%(n-k), b=a+k;
 array<unsigned char,256> ban{},hit{};for(int i=0;i<n;i++)if(i<a||i>b){int v=p[i];ban[v]=1;for(int h=0;h<8;h++)ban[v^(1<<h)]=1;}
 int goal=p[b];array<array<int,8>,256> dirs{};for(auto&ls:dirs){for(int h=0;h<8;h++)ls[h]=1<<h;shuffle(ls.begin(),ls.end(),rng);}
 P mid{p[a]};long long count=0;
 auto dfs=[&](auto&&self)->void{
  count++;int v=mid.back(),edge=mid.size()-1,rest=n-1-k;int hd=__builtin_popcount(unsigned(v^goal));
  if(hd==1){if(rest+edge+1<96||rest+edge+1>98)return;
   P q(p.begin(),p.begin()+a);q.insert(q.end(),mid.begin(),mid.end());q.insert(q.end(),p.begin()+b,p.end());auto key=can(q);
   if(seen.insert(key).second){assert(verify(q));nnew[q.size()-1]++;seeds.push_back(q);cout<<norm(q,false)<<" "<<job<<" "<<a<<" "<<b<<" "<<can(p)<<endl;}return;}
  if(rest+edge+hd>98||count>=budget)return;
  hit[v]++;for(int h=0;h<8;h++)hit[v^(1<<h)]++;
  for(int dir:dirs[v]){int x=v^dir;if(!ban[x]&&hit[x]==1&&count<budget){mid.push_back(x);self(self);mid.pop_back();}}
  hit[v]--;for(int h=0;h<8;h++)hit[v^(1<<h)]--;
 };dfs(dfs);nodes+=count;
 }cerr<<"parents_at_start "<<start<<" jobs "<<jobs<<" nodes "<<nodes<<" new_96_97_98 "<<nnew[96]<<" "<<nnew[97]<<" "<<nnew[98]<<endl;}
