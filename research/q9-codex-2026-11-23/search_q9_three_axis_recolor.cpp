// Color each time index with one of the four antipodal pairs of Q3.
// Index parity and the retained Q6 position determine which member is used.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
struct Fiber{
    int mask,budget,n,nodes=0;
    Path base,localParity,parent,component,color,times;
    array<Path,512> at;
    vector<Path> adj;
    vector<pair<int,int>> neq;
    Path result,conflict;
    bool trace=false;vector<Path> reason;
    Fiber(const Path& p,int m,int cap,const Path& timeline={}):mask(m),budget(cap),n(p.size()),parent(n),component(n,-1){
        iota(parent.begin(),parent.end(),0);
        times=timeline.empty()?parent:timeline;assert(times.size()==p.size());
        for(int i=0;i<n;i++){
            int x=p[i]&~mask;base.push_back(x);at[x].push_back(i);
            localParity.push_back((times[i]+popcount(unsigned(x)))%2);
        }
    }
    int root(int i){while(parent[i]!=i){parent[i]=parent[parent[i]];i=parent[i];}return i;}
    void link(int i,int j,bool same){
        if(!same){neq.emplace_back(i,j);return;}
        int a=root(i),b=root(j);
        if(a!=b){parent[a]=b;if(trace){reason[i].push_back(j);reason[j].push_back(i);}}
    }
    void explain(int i,int j){
        Path previous(n,-1),queue{i};previous[i]=i;
        for(int t=0;t<queue.size() && previous[j]<0;t++)for(int k:reason[queue[t]])if(previous[k]<0){
            previous[k]=queue[t];queue.push_back(k);
        }
        for(int v=j;v!=i;v=previous[v]){assert(v>=0);conflict.push_back(v);}
        conflict.push_back(i);
    }
    bool prepare(){
        if(trace)reason.resize(n);
        for(int i=0;i<n;i++){
            int x=base[i];
            for(int j:at[x])if(j<i){
                bool same=localParity[j]!=localParity[i] && times[i]!=times[j]+1;
                link(i,j,same);
            }
            for(int b=1;b<512;b*=2)if(!(mask&b)){
                for(int j:at[x^b])if(j<i && localParity[i]==localParity[j])link(i,j,times[i]==times[j]+1);
            }
        }
        int k=0;
        for(int i=0;i<n;i++){int r=root(i);if(component[r]<0)component[r]=k++;component[i]=component[r];}
        vector<array<uint64_t,4>> seen(k);adj.resize(k);color.assign(k,-1);
        for(auto [i,j]:neq){
            int a=component[i],b=component[j];if(a==b){if(trace)explain(i,j);return false;}
            uint64_t bit=uint64_t(1)<<(b%64);
            if(seen[a][b/64]&bit)continue;
            seen[a][b/64]|=bit;seen[b][a/64]|=uint64_t(1)<<(a%64);
            adj[a].push_back(b);adj[b].push_back(a);
        }
        return true;
    }
    int solve(int left,int used){
        if(!left)return 1;if(++nodes>budget)return -1;
        int chosen=-1,score=-1,forbidden=0;
        for(int i=0;i<adj.size();i++)if(color[i]<0){
            int blocked=0,open=0;for(int j:adj[i]){if(color[j]<0)open++;else blocked|=1<<color[j];}
            if(blocked==15)return 0;
            int priority=256*popcount(unsigned(blocked))+open;
            if(priority>score){chosen=i;score=priority;forbidden=blocked;}
        }
        for(int c=0;c<min(used+1,4);c++)if(!(forbidden&(1<<c))){
            color[chosen]=c;int r=solve(left-1,max(used,c+1));if(r)return r;color[chosen]=-1;
        }
        return 0;
    }
    int run(){
        if(!prepare())return 0;
        int status=solve(adj.size(),0);if(status!=1)return status;
        const int local[4]={0,3,5,6};
        for(int i=0;i<n;i++){
            int z=local[color[component[i]]]^(localParity[i]?7:0);
            int x=base[i],j=0;
            for(int bit=1;bit<512;bit*=2)if(mask&bit){if(z&(1<<j))x|=bit;j++;}
            for(int k=0;k<i;k++){
                auto d=popcount(unsigned(x^result[k]));assert(d>0 && ((d==1)==(times[k]+1==times[i])));
            }
            result.push_back(x);
        }
        return 1;
    }
};
#ifndef Q9_FIBER_LIBRARY
int main(int argc,char**argv){
    if(argc!=3)return 2;int cap=stoi(argv[1]);bool controls=stoi(argv[2]);
    string w;int rows=0;uint64_t passes=0,unknown=0,cases=0,visited=0;
    while(cin>>w){
        Path p{0};for(char c:w){if(c<'0'||c>'8')return 2;p.push_back(p.back()^(1<<(c-'0')));}
        for(int mask=1;mask<512;mask++)if(popcount(unsigned(mask))==3){
            Fiber f(p,mask,cap);int r=f.run();cases++;visited+=f.nodes;unknown+=r<0;passes+=r==1;
            if(controls&&r!=1)return 4;
            if(r==1&&!controls){cout<<"FOUND "<<p.size()-1;for(int x:f.result)cout<<" "<<x;cout<<endl;return 0;}
        }
        if(++rows%50==0)cout<<"AT "<<rows<<" "<<cases<<" "<<passes<<" "<<unknown<<" "<<visited<<endl;
    }
    cout<<"DONE "<<rows<<" "<<cases<<" "<<passes<<" "<<unknown<<" "<<visited<<endl;
}

#endif
