#include <array>
#include <algorithm>
#include <bit>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Seq=vector<int>;
int weight(int x){return popcount(unsigned(x));}
bool induced(const Seq&p){for(int j=1;j<int(p.size());j++)for(int i=0;i<j;i++){int d=weight(p[i]^p[j]);if(d==0||(d==1)!=(i+1==j))return false;}return true;}
struct Scan{
 array<int,512>blocked{};array<int,9> code{}; Seq steps,embedding;long long calls=0;
 bool next(int i,int position,int free){
  calls++;
  if(i==int(steps.size()))return true;
  int a=steps[i],literal=code[a];
  int candidates=literal?literal:free;
  while(candidates){int d=candidates&-candidates;candidates^=d;int v=position^d;if(blocked[v])continue;
   code[a]=d;embedding.push_back(v);
   if(next(i+1,v,literal?free:(free^d)))return true;
   code[a]=literal;embedding.pop_back();
  }return false;
 }
};
int main(){string line;int row=0;long long partitions=0,placements=0,total=0;
 while(getline(cin,line)){istringstream f(line);Seq p;int y;while(f>>y)p.push_back(y);if(p.empty())continue;
  for(int i=1;i<int(p.size());i++){
   Seq a(p.begin(),p.begin()+i),b(p.begin()+i,p.end());if(!induced(a)||!induced(b))continue;
   if(a.size()<b.size())a.swap(b);partitions++;
   for(int flip=0;flip<2;flip++,reverse(a.begin(),a.end()))for(int rev=0;rev<2;rev++,reverse(b.begin(),b.end())){
    Scan s;for(int j=1;j<int(b.size());j++)s.steps.push_back(countr_zero(unsigned(b[j]^b[j-1])));
    for(int v=0;v<512;v++)for(int x:a)if(weight(v^x)<=1)s.blocked[v]++;
    for(int m=0;m<512;m++)if(weight(m^a.back())==1&&s.blocked[m]==1){
     for(int d=1;d<=256;d*=2)s.blocked[m^d]++;s.blocked[m]++;
     for(int j=0;j<9;j++){int x=m^(1<<j);if(s.blocked[x]!=1)continue;placements++;s.embedding={x};
      if(s.next(0,x,511)){auto w=a;w.push_back(m);w.insert(w.end(),s.embedding.begin(),s.embedding.end());if(!induced(w))abort();cout<<"FOUND row "<<row<<"\nPATH";for(int v:w)cout<<" "<<v;cout<<endl;return 0;}
     }
     for(int d=1;d<=256;d*=2)s.blocked[m^d]--;s.blocked[m]--;
    }total+=s.calls;
   }
  }row++;
 }cout<<"DONE rows "<<row<<" partitions "<<partitions<<" placements "<<placements<<" recursion "<<total<<endl;
}
