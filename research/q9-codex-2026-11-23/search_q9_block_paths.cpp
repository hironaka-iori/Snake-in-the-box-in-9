// Longest induced path within a prescribed Q9 host via its biconnected components.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
using Path=vector<int>;
struct BlockSearch{
    int goal,limit,timer=0,upper=0;uint64_t nodes=0;bool limited=false;
    array<vector<int>,512> adj;array<int,512> tin{},low{};
    vector<pair<int,int>> stack;vector<Path> blocks;vector<int> weights;vector<Path> tree;
    array<Path,512> arms;Path best;
    void tarjan(int x,int parent){
        tin[x]=low[x]=++timer;
        for(int v:adj[x])if(!tin[v]){
            stack.push_back({x,v});tarjan(v,x);low[x]=min(low[x],low[v]);
            if(low[v]>=tin[x]){
                set<int> members;
                for(;;){auto e=stack.back();stack.pop_back();members.insert(e.first);members.insert(e.second);if(e==make_pair(x,v))break;}
                blocks.emplace_back(members.begin(),members.end());
            }
        }else if(v!=parent&&tin[v]<tin[x]){stack.push_back({x,v});low[x]=min(low[x],tin[v]);}
    }
    int bound(int node,int parent){
        int a=0,b=0;for(int child:tree[node])if(child!=parent){int h=bound(child,node);if(h>a){b=a;a=h;}else b=max(b,h);}
        int w=node>=512?weights[node-512]:0;upper=max(upper,w+a+b+1);return w+a;
    }
    void combine(const Path& a,const Path& middle,const Path& b){
        if(a.size()+middle.size()+b.size()-2<=best.size())return;
        best.assign(a.rbegin(),a.rend());best.insert(best.end(),middle.begin()+1,middle.end());best.insert(best.end(),b.begin()+1,b.end());
    }
    void vertex(int x,int parent){
        arms[x]={x};if(best.empty())best=arms[x];
        for(int child:tree[x])if(child!=parent){
            Path branch=block(child,x);if(best.size()>=goal)return;
            combine(arms[x],Path{x},branch);
            if(branch.size()>arms[x].size())arms[x]=std::move(branch);
            if(best.size()>=goal)return;
        }
    }
    Path block(int id,int parent){
        Path members=blocks[id-512],result{parent};
        for(int v:members)if(v!=parent){vertex(v,id);if(best.size()>=goal)return result;}
        bitset<512> domain;for(int v:members)domain.set(v);
        Path singleton{parent};auto tail=[&](int v)->const Path&{return v==parent?singleton:arms[v];};
        stable_sort(members.begin(),members.end(),[&](int a,int b){return tail(a).size()>tail(b).size();});
        int perStart=max(4,limit/int(members.size()));
        for(int start:members){
            Path walk;array<int,512> touch{};bitset<512> used;int calls=0;
            auto visit=[&](auto&& self,int v)->void{
                if(++calls>perStart){limited=true;return;}
                nodes++;walk.push_back(v);used.set(v);for(int u:adj[v])touch[u]++;
                if(walk.size()>1){
                    combine(tail(start),walk,tail(v));
                    if(start==parent && walk.size()+tail(v).size()-1>result.size()){
                        result=walk;result.insert(result.end(),tail(v).begin()+1,tail(v).end());}
                    if(v==parent && walk.size()+tail(start).size()-1>result.size()){
                        result.assign(walk.rbegin(),walk.rend());result.insert(result.end(),tail(start).begin()+1,tail(start).end());}
                }
                for(int u:adj[v])if(domain[u]&&!used[u]&&touch[u]==1){
                    if(best.size()>=goal||calls>perStart)break;
                    self(self,u);
                }
                for(int u:adj[v])touch[u]--;used.reset(v);walk.pop_back();
            };
            visit(visit,start);if(best.size()>=goal)break;
        }return result;
    }
    void run(const Path& vertices){
        bitset<512> domain;for(int v:vertices)domain.set(v);
        for(int v:vertices)for(int i=0;i<9;i++)if(domain[v^(1<<i)])adj[v].push_back(v^(1<<i));
        Path roots;for(int v:vertices)if(!tin[v]){roots.push_back(v);tarjan(v,-1);}
        tree.resize(512+blocks.size());
        for(int k=0;k<blocks.size();k++){
            auto& members=blocks[k];bitset<512> here,packed;int odd=0,stars=0;bool cycle=members.size()>2;
            for(int v:members){here.set(v);odd+=popcount(unsigned(v))%2;tree[v].push_back(512+k);tree[512+k].push_back(v);}
            for(int v:members){
                int deg=0,n=0;int pick[3];for(int y:adj[v])if(here[y]){deg++;if(n<3&&!packed[y])pick[n++]=y;}
                cycle&=deg==2;
                if(n==3&&!packed[v]){stars++;packed.set(v);for(int y:pick)packed.set(y);}
            }
            int n=members.size();weights.push_back(min(n-max(stars,int(cycle)),2*min(odd,n-odd)+1)-1);
        }
        for(int r:roots)bound(r,-1);if(upper<goal)return;
        for(int r:roots){vertex(r,-1);if(best.size()>=goal)return;}
    }
};
int main(int argc,char**argv){
    if(argc!=3)return 2;int goal=stoi(argv[1])+1,limit=stoi(argv[2]);string l;
    while(getline(cin,l)){Path domain;int v;istringstream in(l);bitset<512> seen;
        while(in>>v){if(v<0||v>=512||seen[v])return 2;seen.set(v);domain.push_back(v);}
        BlockSearch q;q.goal=goal;q.limit=limit;q.run(domain);
        if(q.best.size()>=goal){
            cout<<"FOUND";for(int i=0;i<goal;i++){for(int j=0;j<i;j++)assert(q.best[i]!=q.best[j] && (popcount(unsigned(q.best[i]^q.best[j]))==1)==(i==j+1));cout<<" "<<q.best[i];}
        }else cout<<(q.limited?"UNKNOWN":"NO")<<" "<<q.nodes;
        cout<<endl;
    }
}
