#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Node{array<int,8> child{};};vector<Node>trie(1);
array<int,8>mapping;array<bool,256>forbidden{},isolated{};vector<int>arm,bridge;string donorWord;
int donor,choice,global;long long nodes,legal,full,geometries=0,transforms=0;
void witness(){
 int edges=int(arm.size()+bridge.size());if(edges<=global)return;
 vector<int>p=arm;for(int v:bridge)p.push_back(256+v);p.push_back(bridge.back());
 assert(int(p.size())==edges+1);for(int j=0;j<p.size();j++)for(int i=0;i<j;i++)assert(p[i]!=p[j]&&((popcount(unsigned(p[i]^p[j]))==1)==(i+1==j)));
 global=edges;cout<<"BEST "<<edges<<" "<<donor<<" "<<choice<<" "<<bridge.back();for(int v:p)cout<<" "<<v;cout<<endl;
}
void visit(int node,int v,int assigned,int axes){
 nodes++;
 if(bridge.size()>=2&&isolated[v]){legal++;if(bridge.size()>=93)full++;witness();}
 for(int d=0;d<=min(assigned,7);d++){int id=trie[node].child[d];if(!id)continue;
  if(d<assigned){int y=v^(1<<mapping[d]);if(forbidden[y])continue;bridge.push_back(y);visit(id,y,assigned,axes);bridge.pop_back();}
  else for(int avail=255^axes;avail;avail&=avail-1){int bit=avail&-avail;int y=v^bit;if(forbidden[y])continue;
   mapping[d]=countr_zero(unsigned(bit));bridge.push_back(y);visit(id,y,assigned+1,axes|bit);bridge.pop_back();}
 }
}
int main(int argc,char**argv){assert(argc==3);int minRemaining=stoi(argv[2]);vector<string>words;ifstream f(argv[1]);string w;while(f>>w)words.push_back(w);
 for(auto s:words)for(int h=0;h<2;h++){if(h)reverse(s.begin(),s.end());for(int a=0;a+minRemaining<=s.size();a++){
  int node=0,seen=0;array<int,8>names;names.fill(-1);for(int j=a;j<s.size();j++){int d=s[j]-'0';if(names[d]==-1)names[d]=seen++;
   int code=names[d];if(!trie[node].child[code]){trie[node].child[code]=trie.size();trie.emplace_back();}node=trie[node].child[code];}transforms++;}}
 cout<<"TRIE "<<trie.size()<<" directed_starts "<<transforms<<" minimum_remaining "<<minRemaining<<endl;
 for(donor=0;donor<words.size();donor++){
  vector<int>p{0};for(char c:words[donor])p.push_back(p.back()^(1<<(c-'0')));
  isolated.fill(true);for(int v:p){isolated[v]=false;for(int d=0;d<8;d++)isolated[v^(1<<d)]=false;}
  int spare=count(isolated.begin(),isolated.end(),true);if(!spare)continue;
  for(choice=0;choice<=1;choice++){
   geometries+=spare;arm=p;if(choice==0)reverse(arm.begin(),arm.end());int t=arm.back();forbidden.fill(false);for(int v:arm)forbidden[v]=true;forbidden[t]=false;bridge={t};
   visit(0,t,0,0);
  }
 }
 cout<<"DONE "<<geometries<<" geometries "<<nodes<<" visited_prefixes "<<legal<<" legal_bridges "<<full<<" legal_92plus_upper_edges best "<<global<<endl;
}
