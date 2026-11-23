#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Problem{
 array<unsigned char,512> used{},touch{};
 vector<int> middle,left,right;
 int threshold;
 uint64_t nodes=0;
 void mark(int v,int s){used[v]+=s;for(int i=0;i<9;i++)touch[v^(1<<i)]+=s;}
 vector<int> witness(){
  vector<int> p(left.rbegin(),left.rend());p.insert(p.end(),middle.begin(),middle.end());p.insert(p.end(),right.begin(),right.end());return p;
 }
 bool walk(int which){
  nodes++;if(int(left.size()+middle.size()+right.size())>=threshold+1)return true;
  if(which==0&&walk(1))return true;
  auto& part=which==0?left:right;int tip=part.empty()?(which==0?middle.front():middle.back()):part.back();
  for(int d=0;d<9;d++){int x=tip^(1<<d);if(used[x]||touch[x]!=1)continue;
   mark(x,1);part.push_back(x);if(walk(which))return true;
   part.pop_back();mark(x,-1);
  }
  return false;
 }
};
int main(int n,char**av){string w;while(cin>>w){
 Problem p;p.threshold=stoi(av[1]);p.middle.push_back(0);for(char c:w)p.middle.push_back(p.middle.back()^(1<<(c-'0')));for(auto x:p.middle)p.mark(x,1);
 for(int i=0;i<p.middle.size();i++)assert(p.touch[p.middle[i]]==1+(i>0&&i+1<p.middle.size()));
 bool found=p.walk(0);cout<<(found?"FOUND":"COMPLETE")<<" "<<p.nodes<<" "<<w;
 if(found){auto path=p.witness();for(int v:path)cout<<" "<<v;}cout<<endl;
}}
