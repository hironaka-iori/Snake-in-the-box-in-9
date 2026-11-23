// No quotienting: use every ordered Q5 path starting at zero as a possible next visit.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
#include <string>
using namespace std;
using U=uint32_t;
struct Visit{U mask,forbidden;int size;};
vector<Visit> shapes;int dimension=5;
array<int,32> touches{};array<bool,32> taken{};
void walk(int x,U pts){
 U exit=0;for(int v=0;v<(1<<dimension);v++)if(pts&(U(1)<<v))exit|=U(1)<<(v^x);
 shapes.push_back({pts,exit&~U(1),popcount(pts)});
 for(int d=0;d<dimension;d++)touches[x^(1<<d)]++;
 for(int d=0;d<dimension;d++){int y=x^(1<<d);if(taken[y]||touches[y]!=1)continue;
  taken[y]=true;walk(y,pts|(U(1)<<y));taken[y]=false;
 }for(int d=0;d<dimension;d++)touches[x^(1<<d)]--;
}
int main(int argc,char**argv){
 if(argc>1)dimension=stoi(argv[1]);if(dimension<1||dimension>5)return 2;
 int maxVisits=argc>2?stoi(argv[2]):20;
 taken[0]=true;walk(0,1);int n=shapes.size();vector<int>order(n),score(n),next(n);iota(order.begin(),order.end(),0);
 for(int visits=1;visits<=maxVisits;visits++){
  if(visits>1)stable_sort(order.begin(),order.end(),[&](int a,int b){return score[a]>score[b];});
  for(int i=0;i<n;i++){
   int m=0;if(visits>1)for(int j:order)if(!(shapes[i].forbidden&shapes[j].mask)){m=score[j];break;}
   next[i]=shapes[i].size+m;
  }score.swap(next);cout<<"VISITS "<<visits<<" MAX_VERTICES "<<*max_element(score.begin(),score.end())<<endl;
 }
}
