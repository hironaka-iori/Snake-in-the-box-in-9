// Independent direct relative-isometry search; no port quotient or distance signature.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <vector>
using namespace std;
int main(){
 int n,m;while(cin>>n>>m){
 vector<int>a(n),b(m);array<int,256>A{},B{},da{},db{};
 for(int&x:a){cin>>x;A[x]=1;}for(int&x:b){cin>>x;B[x]=1;}
 for(int x:a)for(int d=0;d<8;d++)da[x]+=A[x^1<<d];
 for(int x:b)for(int d=0;d<8;d++)db[x]+=B[x^1<<d];
 vector<int> axes{0,1,2,3,4,5,6,7};bool found=false;long long tests=0;
 do{int tab[256]{};for(int x=1;x<256;x++)tab[x]=tab[x&(x-1)]^(1<<axes[countr_zero(unsigned(x))]);
 for(int sh=0;sh<256;sh++){tests++;bool ok=true;int overlap=0;
  for(int v:b){int w=tab[v]^sh;if(A[w]){if(da[w]>=2||db[v]>=2){ok=false;break;}overlap++;}else if(!db[v]){ok=false;break;}}
  if(!ok||!overlap)continue;
  array<int,512>present{};for(int v:a)present[v]=1;for(int v:b)present[256+(tab[v]^sh)]=1;
  int ends=0,tip=-1;for(int v=0;v<512;v++)if(present[v]){int deg=0;for(int d=0;d<9;d++)deg+=present[v^1<<d];if(deg==1){ends++;tip=v;}if(!deg||deg>2){ok=false;break;}}
  if(!ok||ends!=2)continue;
  int count=0,prev=-1;while(tip!=-1){count++;int z=-1;for(int d=0;d<9;d++){int u=tip^(1<<d);if(present[u]&&u!=prev){z=u;break;}}prev=tip;tip=z;}
  if(count==n+m){found=true;break;}
 }
 if(found)break;
 }while(next_permutation(axes.begin(),axes.end()));
 cout<<int(found)<<" "<<tests<<endl;
 }}
