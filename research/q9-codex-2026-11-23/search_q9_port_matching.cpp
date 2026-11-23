// Match the two ends of each retained island, using mutually chord-free bridges.
#define main short_route_cli
#include "search_q9_short_route_join.cpp"
#undef main
struct Bridge {int a,b; Route r;};
struct Ports {
    Join maker;vector<Path> islands;vector<int> port,selected,parent;
    vector<vector<int>> options;vector<Bridge> edges;
    Path witness;uint64_t nodes=0;int budget,routeCap,goal;
    bool cutoff=false,incomplete=false;
    int root(int x){while(parent[x]!=x)x=parent[x];return x;}
    void make(int a,int b,int upper){
        int target=b<0?-1:port[b],lower=b<0?0:distanceQ(port[a],target);
        vector<Route> routes;Path interior;maker.limited=false;
        for(int l=lower;l<=upper;l+=(b<0?1:2)){
            maker.fill(port[a],target,l,interior,routes);
            if(maker.limited){incomplete=true;break;}
        }
        for(auto& r:routes){
            int id=edges.size();options[a].push_back(id);if(b>=0)options[b].push_back(id);
            edges.push_back({a,b,std::move(r)});
        }
    }
    bool reconstruct(){
        int start=-1;
        for(int i=0;i<port.size();i++)if(edges[selected[i]].b<0){start=i;break;}
        if(start<0)abort();auto prefix=edges[selected[start]].r.path;
        witness.assign(prefix.rbegin(),prefix.rend());
        int cur=start,visits=0;
        while(cur>=0){
            visits++;auto& island=islands[cur/2];
            if(cur%2)witness.insert(witness.end(),island.rbegin(),island.rend());
            else witness.insert(witness.end(),island.begin(),island.end());
            int exit=cur^1;auto& e=edges[selected[exit]];
            if(exit==e.a){witness.insert(witness.end(),e.r.path.begin(),e.r.path.end());cur=e.b;}
            else{witness.insert(witness.end(),e.r.path.rbegin(),e.r.path.rend());cur=e.a;}
        }
        assert(visits==islands.size()&&witness.size()==goal+1&&valid(witness));return true;
    }
    bool fill(Bits blocked,int freeEnds,int need,int remaining){
        if(++nodes>budget){cutoff=true;return false;}
        if(!remaining)return need==0&&freeEnds==0&&reconstruct();
        if(need<0||freeEnds>remaining)return false;
        int next=-1,sumLo=0,sumHi=0,canEnd=0;vector<int> best;
        for(int i=0;i<port.size();i++)if(selected[i]<0){
            vector<int> available;int lo=99999,hi=0;bool can=false;
            for(int id:options[i]){
                auto& e=edges[id];int other=e.a==i?e.b:e.a;
                if(other<0&&!freeEnds)continue;
                if(other>=0&&(selected[other]>=0||root(i/2)==root(other/2)))continue;
                int len=e.r.path.size();
                if(len>need||contact(blocked,e.r.set))continue;
                available.push_back(id);can|=other<0;
                int value=len*(other<0?2:1);lo=min(lo,value);hi=max(hi,value);
            }
            if(available.empty())return false;
            canEnd+=can;sumLo+=lo;sumHi+=hi;
            if(next<0||available.size()<best.size()){next=i;best=std::move(available);}
        }
        if(2*need<sumLo||2*need>sumHi||canEnd<freeEnds)return false;
        for(int id:best){
            auto& e=edges[id];int other=e.a==next?e.b:e.a;
            Bits block=blocked;for(int k=0;k<8;k++)block[k]|=e.r.boundary[k];
            int old=-1;selected[next]=id;
            if(other>=0){selected[other]=id;old=root(other/2);parent[old]=root(next/2);}
            if(fill(block,freeEnds-(other<0),need-int(e.r.path.size()),remaining-(other<0?1:2)))return true;
            if(other>=0){parent[old]=old;selected[other]=-1;}
            selected[next]=-1;if(cutoff)return false;
        }
        return false;
    }
    bool run(const Path& p,const vector<pair<int,int>>& pieces,int target,int bridge,int arm,int cap,int maxOpts){
        budget=cap;goal=target;maker.perPool=maxOpts;
        int kept=0;
        for(auto [a,b]:pieces){
            Path island(p.begin()+a,p.begin()+b+1);if(island.size()<2||!valid(island))return false;
            for(int v:island)if(maker.used[v]||maker.touch[v])return false;
            for(int v:island)maker.mark(v,1);kept+=island.size();
            port.push_back(island.front());port.push_back(island.back());islands.push_back(std::move(island));
        }
        options.resize(port.size());selected.assign(port.size(),-1);parent.resize(islands.size());iota(parent.begin(),parent.end(),0);
        for(int i=0;i<port.size();i++){
            for(int j=i+1;j<port.size();j++)if(i/2!=j/2)make(i,j,bridge);
            make(i,-1,arm);
        }
        Bits blocked{};return fill(blocked,2,goal+1-kept,port.size());
    }
};
#ifndef PORTS_LIBRARY
int main(int argc,char**argv){
    if(argc!=9)return 2;
    int tries=stoi(argv[1]),target=stoi(argv[2]),gap=stoi(argv[3]),fixed=stoi(argv[4]),bridge=stoi(argv[5]),arm=stoi(argv[6]),cap=stoi(argv[7]);
    mt19937 rng(stoi(argv[8]));vector<Path> bank;string line;
    while(getline(cin,line)){Path p{0};for(char c:line){if(c<'0'||c>'8')return 2;p.push_back(p.back()^(1<<(c-'0')));}if(!valid(p))return 3;bank.push_back(p);}
    uint64_t cuts=0,partial=0,nodes=0;
    for(int t=0;t<tries;t++){
        int id=rng()%bank.size();auto& p=bank[id];int n=p.size(),i=rng()%3;
        vector<pair<int,int>> pieces;
        while(i<n-2){int j=min(n-1,i+2+int(rng()%fixed));pieces.push_back({i,j});i=j+2+rng()%gap;}
        Ports ports;bool found=ports.run(p,pieces,target,bridge,arm,cap,120);
        cuts+=ports.cutoff;partial+=ports.incomplete;nodes+=ports.nodes;
        if(found){cout<<"FOUND "<<id<<" "<<t;for(int v:ports.witness)cout<<" "<<v;cout<<endl;return 0;}
        if((t+1)%1000==0||t+1==tries)cout<<"AT "<<t+1<<" "<<cuts<<" "<<partial<<" "<<nodes<<endl;
    }
}

#endif
