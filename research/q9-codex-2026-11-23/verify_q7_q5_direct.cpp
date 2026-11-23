// Direct DFS in Q7 using the target high-coordinate word 5,6,5.
// Introduce Q5 axis names in order to quotient coordinate names.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
using namespace std;
array<int,128> contacts{};array<bool,128> in{};uint64_t countBy[57]{},nodes=0;
string word;ofstream output;
void toggle(int x,int delta){in[x]=delta>0;for(int j=0;j<7;j++)contacts[x^(1<<j)]+=delta;}
void dfs(int x,int layer,int local,int prior,int named,int threshold){
 nodes++;
 const int chainMax[]={0,14,26,39}; // Safe replaceable bound for future layers.
 if(prior+14+chainMax[3-layer]<threshold)return;
 if(layer==3&&prior+local>=threshold){output<<word<<'\n';countBy[prior+local]++;}
 for(int d=0;d<=5;d++){
    bool cross=d==5;
    if(cross&&layer==3)continue;
    if(!cross&&d>named)continue;
    if(cross&&prior+local+chainMax[3-layer]<threshold)continue;
    int axis=cross?(layer==1?6:5):d,y=x^(1<<axis);
    if(in[y]||contacts[y]!=1)continue;
    toggle(y,1);word.push_back('0'+axis);
    dfs(y,layer+int(cross),cross?1:local+1,cross?prior+local:prior,named+int(!cross&&d==named),threshold);
    word.pop_back();toggle(y,-1);
 }
}
int main(int argc,char**argv){if(argc!=3)return 2;output.open(argv[2]);if(!output)return 3;
 int threshold=stoi(argv[1]);toggle(0,1);dfs(0,0,1,0,0,threshold);
 for(int i=threshold;i<=52;i++)cout<<"ROWS "<<i<<" "<<countBy[i]<<endl;
 cout<<"DONE "<<nodes<<endl;
}
