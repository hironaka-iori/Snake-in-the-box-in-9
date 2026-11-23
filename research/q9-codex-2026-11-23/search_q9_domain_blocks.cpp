// Exact induced-path DFS within a vertex domain. Every continuation visits
// consecutive biconnected blocks along a single branch of the block-cut tree.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
struct Search {
    array<vector<int>,512> adj;
    array<int,512> ban{},num{},lo{};
    vector<pair<int,int>> stack;
    vector<int> path,answer;
    int goal,tick; long long cap,nodes=0;
    int tarjan(int x,int parent){
        num[x]=lo[x]=++tick;
        int tail=0;
        for(int y:adj[x]){
            if(ban[y]||y==parent)continue;
            if(!num[y]){
                stack.push_back({x,y});
                int unused=tarjan(y,x);(void)unused;
                lo[x]=min(lo[x],lo[y]);
                if(lo[y]>=num[x]){
                    vector<int> members;
                    while(true){
                        auto [a,b]=stack.back();stack.pop_back();
                        members.push_back(a);members.push_back(b);
                        if(a==x&&b==y)break;
                    }
                    sort(members.begin(),members.end());
                    members.erase(unique(members.begin(),members.end()),members.end());
                    int best=0;
                    for(int v:members)if(v!=x)best=max(best,extra[v]);
                    // Pack disjoint induced stars in this block, never charging
                    // an articulation as the entry of a child block.
                    int missing=0;
                    if(members.size()>=4){
                        ++epoch;for(int v:members)if(v!=x)mark[v]=epoch;
                        for(int v:members)if(mark[v]==epoch){
                            int chosen[3],n=0;
                            for(int z:adj[v])if(mark[z]==epoch){
                                chosen[n++]=z;if(n==3)break;
                            }
                            if(n==3){++missing;mark[v]=0;for(int z:chosen)mark[z]=0;}
                        }
                    }
                    tail=max(tail,(int)members.size()-1-missing+best);
                }
            }else if(num[y]<num[x]){
                lo[x]=min(lo[x],num[y]);stack.push_back({x,y});
            }
        }
        return extra[x]=tail;
    }
    array<int,512> extra{},mark{};long long dummy=0;int epoch=0;
    int bound(int x){
        num.fill(0);tick=0;stack.clear();
        return tarjan(x,-1);
    }
    void dfs(int x){
        if(!answer.empty()||nodes>=cap)return;
        ++nodes;path.push_back(x);
        if((int)path.size()==goal){answer=path;path.pop_back();return;}
        vector<int> next;
        for(int v:adj[x])if(!ban[v])next.push_back(v);
        if(next.empty()||((path.size()==1||next.size()>1) && (int)path.size()+bound(x)<goal)){
            path.pop_back();return;
        }
        ++ban[x];for(int v:adj[x])++ban[v];
        for(int v:next){
            --ban[v];dfs(v);++ban[v];
            if(nodes>=cap||!answer.empty())break;
        }
        --ban[x];for(int v:adj[x])--ban[v];
        path.pop_back();
    }
};
int main(int argc,char**argv){
    if(argc!=3)return 2;
    string line;
    while(getline(cin,line)){
        istringstream in(line);
        Search s;s.goal=stoi(argv[1])+1;s.cap=stoll(argv[2]);
        int idx,v;in>>idx;set<int> domain;while(in>>v)domain.insert(v);
        for(int x:domain)for(int d=0;d<9;d++)if(domain.count(x^(1<<d)))s.adj[x].push_back(x^(1<<d));
        vector<int> starts(domain.begin(),domain.end());
        stable_sort(starts.begin(),starts.end(),[&](int x,int y){return s.adj[x].size()<s.adj[y].size();});
        for(int x:starts){
            s.dfs(x);
            if(!s.answer.empty()||s.nodes>=s.cap)break;
        }
        cout<<idx<<" "<<(!s.answer.empty()?"FOUND":s.nodes>=s.cap?"UNKNOWN":"EXHAUSTED")<<" "<<s.nodes;
        for(int x:s.answer)cout<<" "<<x;
        cout<<endl;
        if(!s.answer.empty())break;
    }
}
