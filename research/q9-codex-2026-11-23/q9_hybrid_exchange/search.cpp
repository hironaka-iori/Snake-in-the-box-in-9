// Every induced path avoids each 3-leaf star and each cycle. Once these have been hit,
// the retained graph consists of paths, whose vertices can be laid out component by component.
#define main original_path_exchange_driver
#include "../search_q9_four_deletions.cpp"
#undef main
#include <set>
#include <cassert>
using Path=vector<int>;
struct Repair{
    int dim,ncube,goal,loss;array<bool,512> original{},alive{};array<int,512> degree{};
    Path removed,result;set<Path> seen;uint64_t forests=0,sets=0,viable=0,complete=0;
    void toggle(int u,int d){alive[u]=d>0;for(int b=1;b<ncube;b*=2)degree[u^b]+=d;}
    Path neighbors(int v)const{Path r;for(int b=1;b<ncube;b*=2)if(alive[v^b])r.push_back(v^b);return r;}
    bool walk(){
        Path id=removed;sort(id.begin(),id.end());if(!seen.insert(id).second)return false;
        Path branch,order;int maximum=2;
        for(int v=0;v<ncube;v++)if(alive[v]&&degree[v]>maximum){maximum=degree[v];branch={v};}
        if(!branch.empty()){
            auto ns=neighbors(branch[0]);sort(ns.begin(),ns.end(),[&](int a,int b){return degree[a]>degree[b];});
            branch.insert(branch.end(),ns.begin(),ns.begin()+3);
        }else{
            array<bool,512> visited{};
            for(int u=0;u<ncube;u++)if(alive[u]&&!visited[u]&&degree[u]<=1){
                for(int v=u;v!=-1;){order.push_back(v);visited[v]=true;int next=-1;
                    for(auto w:neighbors(v))if(!visited[w])next=w;v=next;}
            }
            for(int u=0;u<ncube;u++)if(alive[u]&&!visited[u]){
                Path cycle{u};visited[u]=true;
                for(size_t i=0;i<cycle.size();i++)for(int w:neighbors(cycle[i]))if(!visited[w]){visited[w]=true;cycle.push_back(w);}
                if(branch.empty()||branch.size()>cycle.size())branch=cycle;
            }
        }
        if(!branch.empty()){
            if(int(removed.size())==loss)return false;
            for(int u:branch){
                toggle(u,-1);removed.push_back(u);if(walk())return true;removed.pop_back();toggle(u,1);
            }return false;
        }
        Exchange s{};s.p=order;s.n=s.p.size();s.N=ncube;s.dim=dim;s.k=loss-removed.size();s.gain=goal-s.n;s.fastPairs=true;
        if(s.k>int(order.size())||s.gain+s.k<0)return false;
        s.idx.fill(-1);for(int j=0;j<s.n;j++){s.idx[order[j]]=j;s.toggle(order[j],true);}
        for(int v=0;v<ncube;v++)if(!original[v])s.outside.push_back(v);
        ++forests;bool hit;
        if(s.k==0){s.tested=1;hit=s.add(s.outside,0,s.gain);}
        else hit=s.remove_first(0,s.k);
        sets+=s.tested;viable+=s.viable;complete+=s.trials;
        if(hit){result=s.witness;return true;}return false;
    }
    bool run(const Path& p,int d,int edges,int k){
        dim=d;ncube=1<<d;goal=edges+1;loss=k;
        for(int x:p){assert(x>=0&&x<ncube&&!original[x]);original[x]=true;toggle(x,1);}
        assert(k<int(p.size())&&edges>0&&edges+1+k>=int(p.size()));
        bool hit=walk();
        if(hit){Exchange v{};v.N=ncube;assert(int(result.size())==goal&&v.valid(result));
            assert(count_if(result.begin(),result.end(),[&](int x){return original[x];})==int(p.size())-loss);}
        return hit;
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;int d=stoi(argv[1]),edges=stoi(argv[2]),k=stoi(argv[3]);string line;int row=0;
    while(getline(cin,line)){
        istringstream is(line);Path p;for(int v;is>>v;)p.push_back(v);Repair r;bool ok=r.run(p,d,edges,k);
        cout<<row++<<" "<<ok<<" "<<r.forests<<" "<<r.sets<<" "<<r.viable<<" "<<r.complete;
        for(int v:r.result)cout<<" "<<v;cout<<endl;
    }
}
