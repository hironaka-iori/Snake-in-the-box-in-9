#define main unused_cross_main
// Reuse the piece validator and seam-relative word representation.
#undef main
#define main unused_hinge_main
#include "hinge.cpp"
#undef main
#include <numeric>
struct Node{array<int,9> children{};bool terminal=false;};
struct Solver{
    const vector<Node>& trie;const Path& left;int target;
    array<int,512> halo{},leftWithoutTip{};
    array<int,9> mapping;Path right,solution;uint64_t nodes=0,placements=0,connected=0,deep=0,limits=0;
    Solver(const vector<Node>& t,const Path& p,int n):trie(t),left(p),target(n){
        for(size_t i=0;i<p.size();i++){int x=p[i];for(int z=0;z<=9;z++){
            int y=z==9?x:x^(1<<z);halo[y]++;if(i)leftWithoutTip[y]++;}}
        mapping.fill(-1);
    }
    bool detour(int goal,int required,Path& path,array<int,512>& blocked,int& visits){
        if(++visits>12000)return false;
        int x=path.back(),taken=path.size()-1;
        Path queue{x};array<short,512> prev;prev.fill(-1);prev[x]=x;
        for(size_t i=0;i<queue.size();i++){int v=queue[i];for(int b=1;b<512;b*=2){
            int y=v^b;if(blocked[y]||prev[y]>=0)continue;prev[y]=v;queue.push_back(y);}}
        if(prev[goal]<0||taken+int(queue.size())-1<required)return false;
        Path suffix;for(int y=goal;y!=x;y=prev[y])suffix.push_back(y);
        if(taken+int(suffix.size())>=required){path.insert(path.end(),suffix.rbegin(),suffix.rend());return true;}
        if(popcount(unsigned(x^goal))==1)return false;
        Path options;for(int b=1;b<512;b*=2)if(!blocked[x^b])options.push_back(x^b);
        sort(options.begin(),options.end(),[goal](int a,int b){return popcount(unsigned(a^goal))>popcount(unsigned(b^goal));});
        for(int y:options){
            blocked[x]++;for(int b=1;b<512;b*=2)blocked[x^b]++;
            path.push_back(y);bool hit=detour(goal,required,path,blocked,visits);
            if(hit)return true;path.pop_back();
            blocked[x]--;for(int b=1;b<512;b*=2)blocked[x^b]--;
            if(visits>12000)break;
        }
        return false;
    }
    bool glue(){
        placements++;
        int goal=right[0];Path bridge;
        if(popcount(unsigned(goal))==1)bridge={0,goal};
        else{
            auto blocked=leftWithoutTip;
            for(size_t i=1;i<right.size();i++){int x=right[i];blocked[x]++;for(int bit=1;bit<512;bit*=2)blocked[x^bit]++;}
            blocked[0]=blocked[goal]=0;array<short,512> parent;parent.fill(-1);parent[0]=0;Path queue{0};
            for(size_t i=0;i<queue.size()&&parent[goal]<0;i++){
                int x=queue[i];for(int b=1;b<512;b*=2){int y=x^b;
                    if(blocked[y]||parent[y]>=0)continue;parent[y]=x;queue.push_back(y);}
            }
            if(parent[goal]<0)return false;
            for(int y=goal;y;y=parent[y])bridge.push_back(y);bridge.push_back(0);reverse(bridge.begin(),bridge.end());
            int required=target-(int(left.size())-1)-(int(right.size())-1);
            if(int(bridge.size())-1<required){
                deep++;bridge={0};int visits=0;
                if(!detour(goal,required,bridge,blocked,visits)){limits+=visits>12000;connected++;return false;}
            }
        }
        connected++;if(int(left.size()+right.size()+bridge.size())-3<target)return false;
        solution=left;reverse(solution.begin(),solution.end());
        solution.insert(solution.end(),bridge.begin()+1,bridge.end());
        solution.insert(solution.end(),right.begin()+1,right.end());assert(valid(solution));
        return true;
    }
    bool extend(int id,int v,int used){
        nodes++;if(trie[id].terminal&&glue())return true;
        for(int d=0;d<9;d++)if(trie[id].children[d]){
            int save=mapping[d],choices=save<0?511^used:1<<save;
            for(int bits=choices;bits;bits&=bits-1){
                int b=bits&-bits,x=v^b;if(halo[x])continue;
                right.push_back(x);mapping[d]=countr_zero(unsigned(b));
                if(extend(trie[id].children[d],x,used|b))return true;
                right.pop_back();mapping[d]=save;
            }
        }return false;
    }
    bool solve(){
        for(int x=1;x<512;x++){
            bool direct=popcount(unsigned(x))==1;
            if(direct?leftWithoutTip[x]>0:halo[x]>0)continue;
            right={x};if(extend(0,x,0))return true;
        }return false;
    }
};
#ifndef DETOUR_LIBRARY
int main(int argc,char**argv){
    if(argc!=7)return 2;ifstream a(argv[1]),b(argv[2]);int target=stoi(argv[3]),lo=stoi(argv[4]),hi=stoi(argv[5]);mt19937 rng(stoul(argv[6]));
    set<string> A,B;string w;while(a>>w)A.insert(w);while(b>>w)B.insert(w);
    assert(!A.empty()&&!B.empty());vector<Node> t(1);
    for(const auto& s:B){int id=0;assert(valid(vertices(s)));for(char c:s){int d=c-'A';int n=t[id].children[d];
        if(!n){n=t.size();t[id].children[d]=n;t.emplace_back();}id=n;}t[id].terminal=true;}
    vector<string> order(A.begin(),A.end());shuffle(order.begin(),order.end(),rng);
    uint64_t visits=0,fits=0,conn=0,tried=0,capped=0;int end=min<int>(hi,order.size());
    for(int i=lo;i<end;i++){
        auto left=vertices(order[i]);Solver s(t,left,target);bool hit=s.solve();visits+=s.nodes;fits+=s.placements;conn+=s.connected;tried+=s.deep;capped+=s.limits;
        if(hit){cout<<"FOUND "<<i<<" "<<s.solution.size()-1;for(int x:s.solution)cout<<" "<<x;cout<<endl;return 0;}
        if(i%10==9)cout<<"AT "<<i+1<<" "<<end<<" "<<visits<<" "<<fits<<" "<<conn<<" "<<tried<<" "<<capped<<endl;
    }
    cout<<"DONE "<<lo<<" "<<end<<" "<<B.size()<<" "<<visits<<" "<<fits<<" "<<conn<<" "<<tried<<" "<<capped<<endl;
}

#endif
