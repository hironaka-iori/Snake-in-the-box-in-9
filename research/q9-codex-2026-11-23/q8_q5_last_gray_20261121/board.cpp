#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
using namespace std;
const int gray[]={0,1,3,7,5,4,6,2};
int chain[]={0,14,26,39,52};
bool occ[256]{};int adj[256]{},target;uint64_t nodes=0,cores=0,counts[57]{};
void setv(int v,int z){occ[v]=z==1;for(int d=0;d<8;d++)adj[v^(1<<d)]+=z;}
int label(int i,int x){return gray[i]*32+x;}
bool fillMiddle(int k,int sum,int local,int x){
 nodes++;if(k==4&&(x%32)==0)return sum>=target;
 if(sum-local+14+chain[4-k]<target)return false;
 for(int d=0;d<=5;d++){
  bool cross=d==5;if(cross&&k==4)continue;if(cross&&sum+chain[4-k]<target)continue;
  int nk=k+cross,y=cross?label(nk,x%32):x^(1<<d);
  if(occ[y]||adj[y]!=1+(nk==4&&y%32==0))continue;
  setv(y,1);bool yes=fillMiddle(nk,sum+1,cross?1:local+1,y);setv(y,-1);if(yes)return true;
 }
 return false;
}
bool isolatedA(int x,int local,int fixed,int root){
 if(fixed+local>=target-46){
  counts[fixed+local]++;int y=label(1,root);if(!occ[y]&&adj[y]==1){setv(y,1);bool yes=fillMiddle(1,fixed+local+1,1,y);setv(y,-1);if(yes)return true;}
 }
 for(int d=0;d<5;d++){int y=x^(1<<d);if(!occ[y]&&adj[y]==1){setv(y,1);bool yes=isolatedA(y,local+1,fixed,root);setv(y,-1);if(yes)return true;}}
 return false;
}
bool outer3(int k,int q,int local,int x,int named){
 if(q-local+14+chain[7-k]+14<target-46)return false;
 if(k==7&&q+14>=target-46){
  for(int r=0;r<32;r++)if(!occ[r]&&adj[r]==0){setv(r,1);bool yes=isolatedA(r,1,q,r);setv(r,-1);if(yes)return true;}
 }
 for(int d=0;d<=5;d++){bool cross=d==5;if(cross&&(k==7||q+chain[7-k]+14<target-46))continue;
  if(!cross&&d>named)continue;int nk=k+cross,y=cross?label(nk,x%32):x^(1<<d);
  if(!occ[y]&&adj[y]==1){setv(y,1);bool yes=outer3(nk,q+1,cross?1:local+1,y,named+(!cross&&d==named));setv(y,-1);if(yes)return true;}
 }
 return false;
}
bool rightEnd(int k,int sum,int local,int x){
 ++nodes;if(k==7&&sum>=target)return true;
 if(sum-local+14+chain[7-k]<target)return false;
 for(int d=0;d<=5;d++){bool cross=d==5;if(cross&&(k==7||sum+chain[7-k]<target))continue;
  int nk=k+cross,y=cross?label(nk,x%32):x^(1<<d);
  if(!occ[y]&&adj[y]==1){setv(y,1);bool yes=rightEnd(nk,sum+1,cross?1:local+1,y);setv(y,-1);if(yes)return true;}
 }
 return false;
}
bool leftEnd(int x,int sum,int next){
 if(sum+39>=target&&!occ[next]&&adj[next]==1){setv(next,1);bool yes=rightEnd(5,sum+1,1,next);setv(next,-1);if(yes)return true;}
 for(int d=0;d<5;d++){int y=x^(1<<d);if(!occ[y]&&adj[y]==1){setv(y,1);bool yes=leftEnd(y,sum+1,next);setv(y,-1);if(yes)return true;}}
 return false;
}
int main(int argc,char**argv){
 if(argc<3)return 2;target=stoi(argv[1]);bool yes=false;if(string(argv[2])=="outer"){
 int s=label(5,0);setv(s,1);yes=outer3(5,1,1,s,0);
 }else{
 ifstream f(argv[2]);string w;while(f>>w){++cores;fill(occ,occ+256,false);fill(adj,adj+256,0);
 int k=1,x=0;setv(label(1,0),1);for(char c:w){int d=c-'0';if(d>=5)k++;else x^=1<<d;
 int p=label(k,x);if(occ[p]||adj[p]!=1)abort();setv(p,1);}
 if(adj[0]!=1)continue;setv(0,1);if(leftEnd(0,w.size()+2,label(5,x))){yes=true;break;}
 }}
 cout<<"DONE target "<<target<<" attained "<<yes<<" cores "<<cores<<" extensions "<<nodes<<" exterior";
 for(int n=target-46;n<55;n++)cout<<" "<<n<<"="<<counts[n];cout<<endl;
}
