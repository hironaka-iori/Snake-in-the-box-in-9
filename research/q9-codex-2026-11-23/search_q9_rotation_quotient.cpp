// A simple induced cycle in the orbit quotient lifts iff it visits every vertex of its orbit union.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
using Bits=bitset<256>;
struct Job{
    int dim,d,g,first,last,k,N;uint64_t cap,nodes=0,closed=0;
    vector<vector<int>> orb;vector<int> path,answer;
    vector<Bits> adj,conflict;vector<vector<int>> neighbors;
    void lift(){
        array<bool,512> in{};for(int i:path)for(int v:orb[i])in[v]=true;
        int start=orb[path[0]][0],v=start,lastv=-1;vector<int> out;
        do{
            out.push_back(v);int next=-1,count=0;
            for(int j=0;j<dim;j++){int w=v^(1<<j);if(in[w]){count++;if(w!=lastv)next=w;}}
            if(count!=2||next<0||int(out.size())>g)abort();
            lastv=v;v=next;
        }while(v!=start);
        if(out.size()==g)answer=out;
    }
    void dfs(int s,int tip,Bits live){
        if(nodes>=cap||!answer.empty())return;
        nodes++;
        if(int(path.size()+live.count())<k)return;
        auto choices=adj[tip]&live;
        bool final=int(path.size())+1==k;
        if(path.size()>1){
            if(final)choices&=adj[s];
            else choices&=~conflict[s];
        }
        auto nextLive=live&~conflict[tip];
        for(int w:neighbors[tip])if(w>s&&choices[w]){
            if(final && w<=path[1])continue;
            path.push_back(w);
            if(final){closed++;lift();}
            else{Bits next=nextLive;next.reset(w);dfs(s,w,next);}
            path.pop_back();
            if(nodes>=cap||!answer.empty())break;
        }
    }
    void run(){
        int flip;cin>>dim>>d>>g>>cap>>first>>last>>flip;
        N=1<<dim;vector<int> perm(dim);for(int &v:perm)cin>>v;
        k=g/d;if(k<3||k*d!=g)abort();
        vector<bool> seen(N);
        for(int x=0;x<N;x++)if(!seen[x]){
            vector<int> o;int y=x;
            while(!seen[y]){
                o.push_back(y);seen[y]=true;int z=flip;
                for(int j=0;j<dim;j++)if(y>>j&1)z^=1<<perm[j];
                y=z;
            }
            if(y!=x)abort();
            if(o.size()!=d)continue;
            bool self=false;for(int z:o)if(popcount(unsigned(z^x))==1)self=true;
            if(!self)orb.push_back(o);
        }
        if(orb.size()>256)abort();
        adj.resize(orb.size());conflict.resize(orb.size());
        for(int i=0;i<int(orb.size());i++)for(int j=0;j<int(orb.size());j++){
            int count=0;for(int v:orb[j])if(popcount(unsigned(v^orb[i][0]))==1)count++;
            adj[i][j]=count==1;conflict[i][j]=count>0;
        }
        neighbors.resize(orb.size());
        for(int i=0;i<int(orb.size());i++)for(int j=0;j<int(orb.size());j++)if(adj[i][j])neighbors[i].push_back(j);
        for(int s=max(0,first);s<int(orb.size())&&(last<0||s<last)&&nodes<cap&&answer.empty();s++){
            if(int(orb.size())-s<k)break;
            Bits domain;for(int j=s+1;j<int(orb.size());j++)domain.set(j);
            for(int t=s+1;t<int(orb.size())&&nodes<cap&&answer.empty();t++)if(adj[s][t]){
                path={s,t};auto live=domain;live.reset(t);dfs(s,t,live);
            }
        }
        cout<<(answer.empty()?(nodes>=cap?"UNKNOWN":"EXHAUSTED"):"FOUND")<<" "<<orb.size()<<" "<<nodes<<" "<<closed;
        for(int v:answer)cout<<" "<<v;cout<<endl;
    }
};
int main(){int marker;while(cin>>marker){Job j{};j.run();}return 0;}
