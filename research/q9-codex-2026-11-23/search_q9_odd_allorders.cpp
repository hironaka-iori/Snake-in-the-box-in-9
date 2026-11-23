// Enumerate alternative orders, connector choices and both free ends of a fixed parity set.
#define main old_odd_cli
#include "search_q9_odd_hamilton.cpp"
#undef main
#include <numeric>
#include <map>
#include <cassert>
struct Orders {
    Odd& odd;
    Path side;
    int n,anchor,root,budget;
    Graph graph;
    map<pair<int,int>,int> ids;
    vector<Path> choices;
    uint64_t nodes=0,calls=0,orders=0,lifts=0;
    bool cutoff=false,count_only=false;
    Orders(Odd& solver,Path vertices,int limit):odd(solver),side(move(vertices)),n(side.size()),
        anchor(n),root(n+1),budget(limit),graph(Path(n+1),limit){
        iota(graph.label.begin(),graph.label.end(),0);
    }
    void connect(int a,int b,int via){
        auto k=minmax(a,b);
        if(!ids.count(k)){
            ids[k]=graph.edges.size();graph.add(a,b,-1);choices.emplace_back();
        }
        choices.at(ids.at(k)).push_back(via);
    }
    bool solve(){
        Search s(side,1);for(int v=0;v<512;v++){
            unsigned m=s.axes[v];int degree=popcount(m);if(degree<1||degree>2)continue;
            int a=s.slot[v^(1<<countr_zero(m))];m&=m-1;
            int b=m?s.slot[v^(1<<countr_zero(m))]:anchor;connect(a,b,v);
        }
        if(graph.adj[anchor].empty())return false;
        int hard=0;
        for(int j=0;j<n;j++){
            if(graph.adj[j].empty())return false;
            if(graph.adj[j].size()==1)hard++;
            connect(j,root,-1);
        }
        if(hard>1)return false;
        connect(anchor,root,-1);
        vector<int8_t> state(graph.edges.size());state.back()=1;
        return visit(state);
    }
    bool visit(vector<int8_t> state){
        graph.limit=budget-int(nodes);graph.nodes=0;graph.witness.clear();if(graph.limit<1){cutoff=true;return false;}
        auto r=graph.visit(state);nodes+=graph.nodes;calls++;
        if(r<0){cutoff=true;return false;}if(!r)return false;
        orders++;
        auto order=graph.witness;
        if(order.back()==anchor)reverse(order.begin(),order.end());
        assert(int(order.size())==n+1 && order.front()==anchor);
        Path used,path;for(int j=1;j<=n;j++){
            used.push_back(ids.at(minmax(order[j-1],order[j])));
            path.push_back(choices[used.back()][0]);path.push_back(side[order[j]]);
        }
        auto vary=[&](auto&&self,int pos)->bool{
            if(pos==n){lifts++;if(count_only){assert(verify191(path));return false;}return odd.inspect(path);}
            for(int x:choices[used[pos]]){
                path[2*pos]=x;if(self(self,pos+1))return true;
            }return false;
        };
        if(vary(vary,0))return true;
        used.push_back(ids.at(minmax(order.back(),root)));
        for(int edge:used)if(!state[edge]){
            state[edge]=-1;if(visit(state))return true;
            if(cutoff)return false;
            state[edge]=1;
        }
        return false;
    }
};
#ifndef Q9_ALL_ORDERS_LIBRARY
int main(int argc,char** argv){
    if(argc!=3 && argc!=4)return 2;bool count_only=argc==4 && string(argv[3])=="counts";int cap=stoi(argv[2]);Odd odd(argv[1],cap);
    string line;uint64_t count=0,orders=0,lifts=0,cuts=0;
    while(getline(cin,line)){
        istringstream in(line);int x;Path t;while(in>>x)t.push_back(x);
        if((!count_only && t.size()!=96)||t.size()<2||set<int>(t.begin(),t.end()).size()!=t.size())return 3;
        for(int v:t)if(v<0||v>=512||(popcount(unsigned(v^t[0]))%2))return 3;
        Orders e(odd,move(t),cap);e.count_only=count_only;bool found=e.solve();if(count_only)cout<<"COUNT "<<e.orders<<" "<<e.lifts<<" "<<e.cutoff<<endl;orders+=e.orders;lifts+=e.lifts;cuts+=e.cutoff;count++;
        if(count%2500==0||found)cout<<"AT "<<count<<" "<<orders<<" "<<lifts<<" "<<cuts<<" "<<odd.novel.size()<<endl;
        if(found)return 0;
    }
    cout<<"DONE "<<count<<" "<<orders<<" "<<lifts<<" "<<cuts<<" "<<odd.novel.size()<<endl;
}

#endif
