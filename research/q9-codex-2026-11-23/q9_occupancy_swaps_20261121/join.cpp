#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <map>
#include <string>
#include <vector>
using namespace std;
struct Join{
 int cap,nodes=0;bool cutoff=false;
 array<int,512>occupied{},contact{};array<int,9> images{};vector<int>p,built;string b;
 bool dfs(int i,int last,int used){
  if(++nodes>cap){cutoff=true;return false;}
  if(i==b.size())return true;int a=b[i]-'0',which=images[a];
  int choices=which<0?(511^used):(1<<which);
  while(choices){int d=countr_zero(unsigned(choices));choices&=choices-1;int y=last^(1<<d);
   if(occupied[y]||contact[y])continue;
   images[a]=d;built.push_back(y);
   if(dfs(i+1,y,used|(1<<d)))return true;
   built.pop_back();images[a]=which;if(cutoff)return false;
  }
  return false;
 }
 bool run(string a,string w){
  if(a=="-")a.clear();if(w=="-")w.clear();p={0};
  for(char c:a)p.push_back(p.back()^(1<<(c-'0')));
  for(int v:p){occupied[v]=1;for(int d=0;d<9;d++)contact[v^(1<<d)]++;}
  for(int orientation=0;orientation<2;orientation++,reverse(p.begin(),p.end())){
   for(int bw=0;bw<2;bw++,reverse(w.begin(),w.end()))for(int d=0;d<9;d++){
    int y=p.back()^(1<<d);if(occupied[y]||contact[y]!=1)continue;
    b=w;images.fill(-1);built={y};if(dfs(0,y,0)){p.insert(p.end(),built.begin(),built.end());return true;}
    if(cutoff)return false;
   }
  }
  return false;
 }
};
int main(int argc,char**argv){int cap=stoi(argv[1]),id=0,exhaust=0,unknown=0;long long nodes=0;string a,b;
 while(cin>>a>>b){Join j{cap};if(j.run(a,b)){
   for(int i=0;i<j.p.size();i++)for(int h=0;h<i;h++)if(j.p[i]==j.p[h]||(popcount(unsigned(j.p[i]^j.p[h]))==1)!=(h+1==i))abort();
   cout<<"PATH "<<j.p.size()-1;for(int v:j.p)cout<<" "<<v;cout<<"\nFOUND "<<id<<endl;return 0;}
  nodes+=j.nodes;exhaust+=!j.cutoff;unknown+=j.cutoff;id++;
 }
 cout<<"DONE "<<id<<" "<<nodes<<" "<<exhaust<<" "<<unknown<<endl;
}
