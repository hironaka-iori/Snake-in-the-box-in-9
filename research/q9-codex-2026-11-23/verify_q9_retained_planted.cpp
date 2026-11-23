#include "q9_seed_growth.hpp"
#include <iostream>
#include <string>
using namespace std;
int main(){
 string w;while(cin>>w){
  int axis=-1;for(char c='0';c<='8';c++)if(count(w.begin(),w.end(),c)==1)axis=c-'0';
  if(axis<0)continue;
  vector<int> p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
  for(int missing:{3,5,7,9}){
   vector<int>a,b;for(int i=(missing+1)/2;i<p.size()-missing/2;i++)((p[i]>>axis)&1?b:a).push_back(p[i]);
   int retained=a.size()+b.size();SeedGrow s;
   if(!s.run(a,b,9,191,512-retained,retained))abort();
   auto&q=s.witness;int inside=0;
   for(int j=0;j<q.size();j++){inside+=int(s.host[q[j]]);for(int i=0;i<j;i++)if(q[i]==q[j]||has_single_bit(unsigned(q[i]^q[j]))!=(i+1==j))abort();}
   if(inside!=retained||q.size()<192||q.size()-inside<missing)abort();
   cout<<"PASS retained "<<inside<<" outside "<<q.size()-inside<<" edges "<<q.size()-1<<endl;
  }return 0;
 }return 2;
}
