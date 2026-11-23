#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Arms {
    array<vector<int>,2> step,arm;
    array<int,512> used{}, degree{};
    array<int,2> axes{};
    uint64_t visited=0,limit;
    bool hit=false,cut=false;
    void mark(int v,int s){used[v]+=s;for(int d=0;d<9;d++)degree[v^(1<<d)]+=s;}
    void push(int side,int v){arm[side].push_back(v);mark(v,1);}
    void pop(int side){mark(arm[side].back(),-1);arm[side].pop_back();}
    bool allowed(int v){return !used[v]&&degree[v]==1;}
    void dfs(){
        if(++visited>limit){cut=true;return;}
        const array<size_t,2> old={arm[0].size(),arm[1].size()};
        auto done=[&](int s){return arm[s].size()>step[s].size();};
        bool bad=false;
        for(int s=0;s<2&&!bad;s++)while(!done(s)){
            int d=step[s][arm[s].size()-1];if((1<<d)&axes[s])break;
            int v=arm[s].back()^(1<<d);if(!allowed(v)){bad=true;break;}push(s,v);
        }
        if(!bad){
            if(done(0)&&done(1)){hit=true;return;}
            int side=-1;vector<int> options;
            for(int s=0;s<2;s++)if(!done(s)){
                vector<int> next;int orig=step[s][arm[s].size()-1];
                for(int i=0;i<9;i++){int v=arm[s].back()^(1<<((orig+i)%9));if(allowed(v))next.push_back(v);}
                if(side==-1||next.size()<options.size()){side=s;options=next;}
            }
            for(int v:options){push(side,v);dfs();if(hit)return;pop(side);if(cut)break;}
        }
        for(int s=0;s<2;s++)while(arm[s].size()>old[s])pop(s);
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int flex=stoi(argv[1]),budget=stoi(argv[2]),shard=stoi(argv[3]);
    string line;
    while(getline(cin,line)){
        istringstream in(line);int id,target,join;in>>id>>target>>join;vector<int>p;int v;
        while(in>>v)p.push_back(v);
        if(p.size()!=target+1||join<0||join+1>=p.size())return 2;
        array<vector<int>,2> steps;
        for(int i=join;i>0;i--)steps[0].push_back(__builtin_ctz(unsigned(p[i]^p[i-1])));
        for(int i=join+1;i+1<p.size();i++)steps[1].push_back(__builtin_ctz(unsigned(p[i]^p[i+1])));
        vector<int> masks;
        for(int m=1;m<512;m++)if(__builtin_popcount(unsigned(m))==flex)masks.push_back(m);
        int tests=0,cuts=0;uint64_t nodes=0;
        for(int a:masks)for(int b:masks){
            if(shard>1 && (unsigned(a*2654435761u+b*2246822519u+id)%shard)!=0)continue;
            Arms s;s.step=steps;s.axes={a,b};s.limit=budget;s.push(0,p[join]);s.push(1,p[join+1]);s.dfs();tests++;cuts+=s.cut;nodes+=s.visited;
            if(s.hit){
                auto q=s.arm[0];reverse(q.begin(),q.end());q.insert(q.end(),s.arm[1].begin(),s.arm[1].end());
                assert(q.size()==p.size());
                for(int j=0;j<q.size();j++)for(int i=0;i<j;i++)assert(q[i]!=q[j]&&((__builtin_popcount(unsigned(q[i]^q[j]))==1)==(j==i+1)));
                cout<<"FOUND "<<id<<" "<<target<<" "<<a<<" "<<b;for(int x:q)cout<<" "<<x;cout<<endl;break;
            }
        }cout<<"ROW "<<id<<" "<<target<<" "<<tests<<" "<<cuts<<" "<<nodes<<endl;
    }
}
