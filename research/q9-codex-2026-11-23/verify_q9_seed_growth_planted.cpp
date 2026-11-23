#include "q9_seed_growth.hpp"
#include <iostream>
#include <string>
using namespace std;
int main(){
 string w;while(cin>>w){
  int bit=-1;for(int d=0;d<9;d++)if(count(w.begin(),w.end(),'0'+d)==1)bit=d;
  if(bit<0)continue;
  vector<int> p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
  for(int e=0;e<=9;e++){
   vector<int>a,b;
   for(int i=(e+1)/2;i<p.size()-e/2;i++)((p[i]>>bit)&1?b:a).push_back(p[i]);
   for(int t=0;t<=e;t++){
    SeedGrow solver;bool ok=solver.run(a,b,9,191,t);if(ok!=(t==e))abort();
    if(ok){auto &q=solver.witness;if(q.size()!=192)abort();
      for(int i=0;i<192;i++)for(int j=0;j<i;j++)if(q[i]==q[j]||has_single_bit(unsigned(q[i]^q[j]))!=(i==j+1))abort();
      cout<<"PASS "<<t<<" outsiders "<<q.size()-1<<" edges "<<solver.nodes<<" nodes"<<endl;
    }
   }
  }return 0;
 }return 2;
}
