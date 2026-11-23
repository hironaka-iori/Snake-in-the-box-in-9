#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){
    if(argc!=6)return 2;ifstream f(argv[1]),g(argv[2]);int n=stoi(argv[3]),trials=stoi(argv[4]);mt19937 rng(stoul(argv[5]));
    string w;vector<string> sources,near;while(f>>w)if(int(w.size())>=(n+1)/2)sources.push_back(w);
    while(g>>w)if(int(w.size())==n)near.push_back(w);
    if(sources.empty()||near.empty())return 2;set<string> seen;
    for(int t=0;t<trials;t++){
        auto m=sources[rng()%sources.size()],q=near[rng()%near.size()];string original=q;
        if(rng()%2)reverse(m.begin(),m.end());if(rng()%2)reverse(q.begin(),q.end());
        int blocks=n/2,len=min(blocks,8+int(rng()%90)),start=rng()%(blocks-len+1),offset=rng()%(m.size()-len+1);
        array<int,9> ds,group; iota(ds.begin(),ds.end(),0);shuffle(ds.begin(),ds.end(),rng);for(int j=0;j<9;j++)group[ds[j]]=j/2;
        int score[8][9]{};
        for(int i=0;i<len;i++){
            int d=m[i+offset]-'0',a=q[2*(start+i)]-'0',b=q[2*(start+i)+1]-'0';
            for(int x=0;x<9;x++)score[d][x]+=(group[x]==group[a]||group[x]==group[b]);
        }
        array<int,512> dp,from;dp.fill(-9999);dp[0]=0;
        for(int mask=0;mask<512;mask++){int d=popcount(unsigned(mask));if(d>=8)continue;
            for(int x:ds)if(!(mask>>x&1)){int dest=mask|1<<x,v=dp[mask]+score[d][x];if(v>dp[dest]){dp[dest]=v;from[dest]=x;}}}
        int mask=511^(1<<ds[0]);for(int x:ds)if(dp[511^(1<<x)]>dp[mask])mask=511^(1<<x);
        array<int,8> image{};for(int i=7;i>=0;i--){int x=from[mask];image[i]=x;mask^=1<<x;}
        int changed=0;
        for(int i=0;i<len;i++){int j=2*(start+i),wanted=image[m[offset+i]-'0'];
            if(group[q[j]-'0']==group[wanted] || group[q[j+1]-'0']==group[wanted])continue;
            q[j+(rng()%2)]='0'+wanted;changed++;}
        if(changed==0||changed>12)continue;
        string layout;for(int x:ds)layout+='0'+x;
        if(!seen.insert(q+layout).second)continue;
        cout<<q<<" "<<layout<<" "<<offset<<" "<<start<<" "<<len<<" "<<changed<<" "<<m<<" ";
        for(int x:image)cout<<x;cout<<"\n";
    }
}
