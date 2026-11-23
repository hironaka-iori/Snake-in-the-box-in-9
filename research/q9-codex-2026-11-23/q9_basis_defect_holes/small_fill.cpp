#include <algorithm>
#include <array>
#include <bitset>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <vector>
using namespace std;
using Bits=bitset<512>;
#include "direct_fill.hpp"
bool paircheck(const vector<int>& v) {
 vector<vector<int>> adj(v.size());int ends=0,start=-1;
 for(unsigned j=0;j<v.size();j++)for(unsigned i=0;i<j;i++)if(__builtin_popcount(v[j]^v[i])==1){adj[j].push_back(i);adj[i].push_back(j);}
 for(unsigned j=0;j<v.size();j++){if(adj[j].size()==1){start=j;ends++;}else if(adj[j].size()!=2)return false;}
 if(ends!=2)return false;
 int at=start,prev=-1,visits=0;
 while(at>=0){int next=-1;for(int n:adj[at])if(n!=prev){next=n;break;}prev=at;at=next;visits++;}
 return visits==(int)v.size();
}
bool brute(vector<int>&v,int remain,int start,Bits &used,long long &tested) {
 if(!remain){tested++;return paircheck(v);}
 for(int x=start;x+remain<=512;x++)if(!used[x]){
   v.push_back(x);used.set(x);bool hit=brute(v,remain-1,x+1,used,tested);used.reset(x);v.pop_back();if(hit)return true;
 }
 return false;
}
int main(){int yes=0,no=0;long long tested=0;mt19937 r(81913);
 for(int i=0;i<48;i++){
    int h=1+i%2;vector<int> p={0,1,3,7,15,31,63,127};shuffle(p.begin(),p.end(),r);p.resize(p.size()-h);
    if(i%4>=2)p.back()^=384;
    if(i%8>=4){for(int& v:p)v^=427;}
    Bits selected;for(int v:p)selected.set(v);if(selected.count()!=p.size())abort();
    DirectFill solve;solve.goal=p.size()+h-1;for(int x:p){solve.toggle(x,true);solve.trail.push_back(x);}
    bool feasible=true;for(int x:p)feasible&=solve.degrees[x]<=2;
    bool found=feasible&&solve.append(h),reference=brute(p,h,0,selected,tested);if(found!=reference)abort();
    if(found){if(!paircheck(solve.answer))abort();yes++;}else no++;
 }
 cout<<"cases "<<yes+no<<" feasible "<<yes<<" infeasible "<<no<<" terminal_candidate_sets "<<tested<<endl;
}
