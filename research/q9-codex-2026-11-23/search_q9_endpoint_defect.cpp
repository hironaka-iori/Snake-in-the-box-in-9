#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Search{
    array<int,512> used{},degree{};
    vector<int> left,right,core,best;int record=1000,target=0,id=0,bestid=-1;long long nodes=0;
    void update(int v,int s){used[v]+=s;for(int k=0;k<9;k++)degree[v^(1<<k)]+=s;}
    void dfs(int l,int r,int score){
        if(score>=record)return;
        nodes++;
        if(!l&&!r){
            record=score;best=left;reverse(best.begin(),best.end());best.insert(best.end(),core.begin(),core.end());best.insert(best.end(),right.begin(),right.end());bestid=id;return;
        }
        bool first=l>0;auto& trail=first?left:right;
        int tip=trail.empty()?(first?core.front():core.back()):trail.back();
        for(int k=0;k<9;k++){
            int v=tip^(1<<k),next=score+degree[v]-1;
            if(used[v]||next>=record)continue;
            update(v,1);trail.push_back(v);dfs(l-int(first),r-int(!first),next);trail.pop_back();update(v,-1);
        }
    }
};
int main(int argc,char**argv){
    if(argc!=2)return 2;int trim=stoi(argv[1]);vector<vector<int>> bank;string word;while(cin>>word){
        vector<int> p{0};for(char a:word)p.push_back(p.back()^(1<<(a-'0')));
        if(p.size()!=192)return 3;
        for(int i=0;i<p.size();i++)for(int j=i+2;j<p.size();j++)assert(__builtin_popcount(unsigned(p[i]^p[j]))>1);
        bank.push_back(p);
    }
    for(int t=192;t<=196;t++){
        Search s;s.target=t;
        for(int id=0;id<bank.size();id++)for(int cut=0;cut<=trim;cut++)for(int a=0;a<=cut;a++){
            s.id=id;s.core.assign(bank[id].begin()+a,bank[id].end()-(cut-a));
            for(int v:s.core)s.update(v,1);
            for(int l=0;l<=t-191+cut;l++)s.dfs(l,t-191+cut-l,0);
            for(int v:s.core)s.update(v,-1);
        }
        cout<<t<<" "<<s.record<<" "<<s.bestid<<" "<<s.nodes;for(auto x:s.best)cout<<" "<<x;cout<<endl;
    }
}
