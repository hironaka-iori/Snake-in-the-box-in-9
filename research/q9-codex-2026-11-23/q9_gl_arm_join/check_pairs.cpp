#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
int main(){int id,bridge;string a,b;
 while(cin>>id>>bridge>>a>>b){long long good=0,tested=0;
  for(int i=0;i<2;i++,reverse(a.begin(),a.end()))for(int j=0;j<2;j++,reverse(b.begin(),b.end())){
   vector<int> p{0};for(char c:a)p.push_back(p.back()^(1<<(c-'0')));
   bool forbid[512]={};for(int k=0;k+1<(int)p.size();k++){int x=p[k]^p.back();forbid[x]=true;for(int d=0;d<9;d++)forbid[x^1<<d]=true;}forbid[0]=true;
   vector<int> origins;if(bridge){for(int d=0;d<9;d++)if(!forbid[1<<d])origins.push_back(1<<d);for(int d=0;d<9;d++)forbid[1<<d]=true;}else origins={0};
   array<int,9> perm; iota(perm.begin(),perm.end(),0);
   do{for(int site:origins){int v=site;bool ok=true;tested++;for(char c:b){v^=1<<perm[c-'0'];if(forbid[v]){ok=false;break;}}good+=ok;}}while(next_permutation(perm.begin(),perm.end()));
  }
  cout<<id<<" "<<bridge<<" "<<tested<<" "<<good<<endl;
 }
}
