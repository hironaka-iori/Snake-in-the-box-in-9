#include <array>
#include <algorithm>
#include <fstream>
#include <iostream>
#include <string>
using namespace std;
array<unsigned char,256> occ,adj;array<array<int,2>,95> pairs;array<array<int,8>,256> nb;long long nodes=0,roots=0;
void update(int x,int d){occ[x]+=d;for(int a:nb[x])adj[a]+=d;}
bool dfs(int n,int v){++nodes;if(n==62)return true;for(int a:pairs[n])if(a>=0){int x=v^(1<<a);if(occ[x]||adj[x]!=1)continue;update(x,1);if(dfs(n+1,x))return true;update(x,-1);}return false;}
int main(){ifstream f("../q9_gap_generations/prior191.words");for(int i=0;i<256;i++)for(int j=0;j<8;j++)nb[i][j]=i^(1<<j);string w;int hits=0;
 while(f>>w)for(int off=0;off+124<=(int)w.size();off++)for(int missing=0;missing<9;missing++){
 for(int j=0;j<62;j++)for(int k=0;k<2;k++){int d=w[off+2*j+k]-'0';pairs[j][k]=d==missing?-1:d-(d>missing);}
 occ.fill(0);adj.fill(0);update(0,1);roots++;if(dfs(0,0))hits++;}
 cout<<"target 62 rooted_omitted_axis_trials "<<roots<<" DFS_nodes "<<nodes<<" hits "<<hits<<endl;
}
