#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using namespace std;using Mask=bitset<512>;
array<Mask,512> hood;string donor,cur;int offset,goal,best,donorId,limit;long long visits,total=0,caps=0,starts=0;ofstream rec;bool shuffled;
void dfs(int j,int v,int used,const Mask&block){
 if(++visits>limit)return;
 if(j>best){best=j;rec<<donorId<<' '<<offset<<' '<<j<<' '<<cur<<' '<<donor.substr(offset,2*j)<<endl;}
 if(j==goal)return;int off=offset+2*j;if(off+1>=(int)donor.size())return;Mask next=block|hood[v];int s=shuffled?((off*1103515245u+donorId)>>20)&1:0;
 for(int k=0;k<2;k++){char c=donor[off+((k+s)&1)];int axis=1<<(c-'0'),u=v^axis;if((used|axis)==511||block[u])continue;cur+=c;dfs(j+1,u,used|axis,next);cur.pop_back();if(visits>=limit||best==goal)return;}
}
int main(int argc,char**argv){if(argc!=5)return 2;limit=stoi(argv[1]);goal=95;rec.open(argv[2]);int take=stoi(argv[3]);shuffled=stoi(argv[4]);for(int v=0;v<512;v++){hood[v].set(v);for(int k=0;k<9;k++)hood[v].set(v^(1<<k));}ifstream f("../q9_gap_generations/prior191.words");for(donorId=0;donorId<take&&f>>donor;donorId++)for(offset=0;offset+2*(best+1)<=(int)donor.size();offset++){++starts;visits=0;cur.clear();dfs(0,0,0,{});caps+=visits>=limit;total+=visits;}cout<<"rows "<<donorId<<" starts "<<starts<<" nodes "<<total<<" capped_starts "<<caps<<" longest_pairs "<<best<<endl;}
