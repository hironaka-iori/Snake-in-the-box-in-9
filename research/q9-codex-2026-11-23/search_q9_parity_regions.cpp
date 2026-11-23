#include <cassert>
// Fix one parity class only. All opposite-parity vertices and their order are free.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <sstream>
struct Bounds{
    array<unsigned char,512> occupied{},load{};
    array<int,512> room{};
    int poor=0,counts[10]{};
    Bounds(){room.fill(9);}
    void change(int x,int sign){
        if(sign<0){poor-=room[x]<2;occupied[x]=false;}
        for(int d=0;d<9;d++){
            int odd=x^(1<<d),prev=load[odd],after=prev+sign;load[odd]=after;
            if(prev)counts[prev]--;if(after)counts[after]++;
            if((prev<=2)==(after<=2))continue;
            int delta=after<=2?1:-1;
            for(int k=0;k<9;k++){int v=odd^(1<<k);int before=room[v];room[v]+=delta;
                if(occupied[v])poor+=(room[v]<2)-(before<2);}
        }
        if(sign>0){occupied[x]=true;poor+=room[x]<2;}
    }
};
#include <random>
struct Region{
    Bounds state;
    vector<int> center,domain,chosen;
    int needed=96;
    uint64_t cap=0,visits=0,exact=0,unknown=0;
    bool limited=false;
    bool fill(const vector<int>& possible,int count){
        if(++visits>cap){limited=true;return false;}
        if(count==0){
            if(state.counts[1]<2||state.counts[2]<needed-1)return false;
            vector<int> set;for(int x=0;x<512;x++)if(state.occupied[x])set.push_back(x);assert(set.size()==needed);
            exact++;Search s(set,100000,false);
            if(s.test())return true;unknown+=s.unknown;return false;
        }
        vector<int> viable;
        for(int x:possible){
            state.change(x,1);if(!state.poor)viable.push_back(x);state.change(x,-1);
        }
        if(int(viable.size())<count)return false;
        for(int i=0;i+count<=int(viable.size());i++){
            int x=viable[i];state.change(x,1);
            if(fill(vector<int>(viable.begin()+i+1,viable.end()),count-1))return true;
            state.change(x,-1);if(limited)return false;
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;int trials=stoi(argv[1]),seed=stoi(argv[2]),cap=stoi(argv[3]),low=stoi(argv[4]);
    vector<vector<int>> sets;string line;while(getline(cin,line)){
        istringstream in(line);vector<int>s;int x;while(in>>x)s.push_back(x);
        if(s.size()!=96||!is_sorted(s.begin(),s.end())||adjacent_find(s.begin(),s.end())!=s.end())return 3;
        sets.push_back(std::move(s));
    }
    mt19937 gen(seed);
    uint64_t cuts=0,nodes=0,exact=0,unknown=0,eligible=0,overfull=0;
    for(int t=0;t<trials;t++){
        const auto&s=sets[gen()%sets.size()];Bounds initial;array<bool,512> remove{};
        for(int v:s)initial.change(v,1);
        int x;
        do{x=gen()%512;}while(initial.occupied[x]||__builtin_parity(unsigned(s[0]^x)));
        int r=low+gen()%10;
        auto free_ports=[&](int p){
            vector<pair<int,int>> ns;
            for(int d=0;d<9;d++){int v=p^(1<<d);ns.push_back({initial.load[v]*int(5+gen()%15)+int(gen()%40),v});}
            sort(ns.begin(),ns.end());
            for(int k=0;k<2;k++){
                vector<int> nb;for(int d=0;d<9;d++){int v=ns[k].second^(1<<d);if(initial.occupied[v]&&!remove[v])nb.push_back(v);}
                shuffle(nb.begin(),nb.end(),gen);for(size_t j=1;j<nb.size();j++)remove[nb[j]]=true;
            }
        };
        free_ports(x);
        // Make room around other weak selected vertices as well as near the new vertex.
        vector<pair<int,int>> order;
        for(int v:s)if(!remove[v]){
            int proximity=popcount(unsigned(v^x));
            int weight=(t%4==0?0:6*proximity)+(t%4==1?0:min(initial.room[v],5)*3);
            order.push_back({weight+int(gen()%32),v});
        }
        sort(order.begin(),order.end());int m=96-order.size();
        if(m>r){overfull++;continue;}
        for(int k=0;m<r;m++,k++)remove[order[k].second]=true;
        Region reach;reach.cap=cap;
        for(int v:s)if(!remove[v])reach.state.change(v,1);
        reach.state.change(x,1);if(reach.state.poor)continue;eligible++;
        vector<int> pool;
        for(int v=0;v<512;v++)if(!reach.state.occupied[v]&&!__builtin_parity(unsigned(v^x)))pool.push_back(v);
        shuffle(pool.begin(),pool.end(),gen);
        if(reach.fill(pool,r-1))return 0;
        nodes+=reach.visits;exact+=reach.exact;unknown+=reach.unknown;cuts+=reach.limited;
        if((t+1)%20000==0)cout<<"AT "<<t+1<<" "<<eligible<<" "<<exact<<" "<<cuts<<endl;
    }
    cout<<"DONE "<<trials<<" "<<overfull<<" "<<eligible<<" "<<nodes<<" "<<exact<<" "<<cuts<<" "<<unknown<<endl;
}
