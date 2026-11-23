// Upper bound for a chordless walk whose axis sequence repeats after p
// steps up to a fixed coordinate permutation. Enumerate exceptional cycle types.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
struct Check {
 int period,threshold,order,maximum=0,exceptional=0;long long seeds=0;
 array<int,9> perm{},power{},word{},firstrep{};array<unsigned char,512> taken{};
 bool legal(int x,int last){if(taken[x])return false;for(int j=0;j<9;++j){int y=x^(1<<j);if(y!=last&&taken[y])return false;}return true;}
 void finish(int vertex){
  ++seeds;array<int,184> more{};int h=0,len=period;array<int,9> w=word;
  while(len<threshold){
   int block=len%period;if(!block)for(int k=0;k<period;k++)w[k]=perm[w[k]];
   int y=vertex^(1<<w[block]);if(!legal(y,vertex))break;
   taken[y]=1;more[h++]=y;vertex=y;++len;
  }
  maximum=max(maximum,len);
  while(h)taken[more[--h]]=0;
 }
 void dfs(int depth,int x){
  if(depth==period){finish(x);return;}
  for(int d=0;d<9;d++){if(depth==0&&!firstrep[d])continue;int y=x^(1<<d);if(!legal(y,x))continue;
   word[depth]=d;taken[y]=1;dfs(depth+1,y);taken[y]=0;
  }
 }
 void checktype(const vector<int>&parts){
  int m=1;for(int k:parts)m=lcm(m,k);
  if(2*m*period<=threshold)return;
  fill(firstrep.begin(),firstrep.end(),0);int at=0,last=0;
  for(int k:parts){if(k!=last)firstrep[at]=1;last=k;
   for(int a=0;a<k;a++)perm[at+a]=at+(a+1)%k;at+=k;}
  exceptional++;taken[0]=1;dfs(0,0);
 }
 void types(int left,int least,vector<int>&v){
  if(!left){checktype(v);return;}
  for(int k=least;k<=left;k++){v.push_back(k);types(left-k,k,v);v.pop_back();}
 }
};
int main(int argc,char**argv){
 int limit=argc>1?stoi(argv[1]):8;for(int p=1;p<=limit;p++){
  Check c;c.period=p;c.threshold=176;vector<int> v;c.types(9,1,v);
  cout<<"period "<<p<<" exceptional types "<<c.exceptional<<" valid representatives tested "<<c.seeds<<" maximum exceptional prefix "<<c.maximum<<endl;
  if(c.maximum>=c.threshold)return 1;
 }
}
