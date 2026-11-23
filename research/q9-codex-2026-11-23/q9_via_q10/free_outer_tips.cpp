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
    Path best;
    int budget=0;
    static void mark(array<int,512>& halo,int x,int delta){
        halo[x]+=delta;
        for(int bit=1;bit<512;bit*=2)halo[x^bit]+=delta;
    }
    bool tails(Path& front,Path& back,const Path& middle,array<int,512>& taken,bool frontOpen){
        if(++budget>10000)return false;
        size_t count=middle.size()+front.size()+back.size();
        if(count>best.size()){
            best.assign(front.rbegin(),front.rend());
            best.insert(best.end(),middle.begin(),middle.end());
            best.insert(best.end(),back.begin(),back.end());
            if(int(count)-1>=target){solution=best;return true;}
        }
        auto& side=frontOpen?front:back;
        int x=side.empty()?(frontOpen?middle.front():middle.back()):side.back();
        for(int b=1;b<512 && budget<10000;b*=2){
            int y=x^b;
            if(taken[y]!=1)continue;
            mark(taken,y,1);side.push_back(y);
            if(tails(front,back,middle,taken,frontOpen))return true;
            side.pop_back();mark(taken,y,-1);
        }
        return frontOpen && budget<10000 && tails(front,back,middle,taken,false);
    }
    bool complete(const Path& bridge){
        deep++;
        Path middle(left.rbegin(),left.rend()),front,back;
        middle.insert(middle.end(),bridge.begin()+1,bridge.end());
        middle.insert(middle.end(),right.begin()+1,right.end());
        array<int,512> taken{};
        for(int x:middle)mark(taken,x,1);
        return tails(front,back,middle,taken,true);
    }
    bool bridges(Path& bridge,array<int,512>& blocked){
        if(++budget>10000)return false;
        int x=bridge.back(),goal=right.front();
        if(popcount(unsigned(x^goal))==1){
            bridge.push_back(goal);bool hit=complete(bridge);bridge.pop_back();return hit;
        }
        Path queue{x};array<bool,512> seen{};seen[x]=true;
        for(size_t i=0;i<queue.size() && !seen[goal];i++)
            for(int b=1;b<512;b*=2){
                int y=queue[i]^b;
                if(!blocked[y]&&!seen[y]){queue.push_back(y);seen[y]=true;}
            }
        if(!seen[goal])return false;
        for(int b=1;b<512 && budget<10000;b*=2){
            int y=x^b;if(blocked[y])continue;
            mark(blocked,x,1);bridge.push_back(y);
            if(bridges(bridge,blocked))return true;
            bridge.pop_back();mark(blocked,x,-1);
        }
        return false;
    }
    bool glue(){
        placements++;budget=0;auto before=deep;
        auto blocked=leftWithoutTip;
        for(size_t i=1;i<right.size();i++)mark(blocked,right[i],1);
        blocked[0]=blocked[right[0]]=0;
        Path walk{0};bool hit=bridges(walk,blocked);
        connected+=deep>before;limits+=budget>=10000;return hit;
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
    if(argc==3 && string(argv[1])=="--plant"){
        ifstream input(argv[2]);string w;int good=0,total=0;
        while(input>>w){
            for(char& c:w)c='A'+(c-'0');
            auto path=vertices(w);assert(valid(path));int seam=93;
            Path a(path.begin()+2,path.begin()+seam+1);reverse(a.begin(),a.end());
            Path b(path.begin()+seam+3,path.end()-2);int shift=a.front();
            for(auto& x:a)x^=shift;
            for(auto& x:b)x^=shift;
            vector<Node> t(1);Solver s(t,a,191);s.right=b;
            bool ok=s.glue();if(ok && valid(s.solution))good++;total++;
        }
        cout<<"CONTROL "<<good<<" "<<total<<endl;return good==total?0:1;
    }
    if(argc!=7)return 2;ifstream a(argv[1]),b(argv[2]);int target=stoi(argv[3]),lo=stoi(argv[4]),hi=stoi(argv[5]);mt19937 rng(stoul(argv[6]));
    set<string> A,B;string w;while(a>>w)A.insert(w);while(b>>w)B.insert(w);
    assert(!A.empty()&&!B.empty());vector<Node> t(1);
    for(const auto& s:B){int id=0;assert(valid(vertices(s)));for(char c:s){int d=c-'A';int n=t[id].children[d];
        if(!n){n=t.size();t[id].children[d]=n;t.emplace_back();}id=n;}t[id].terminal=true;}
    vector<string> order(A.begin(),A.end());shuffle(order.begin(),order.end(),rng);
    uint64_t visits=0,fits=0,conn=0,tried=0,capped=0;int end=min<int>(hi,order.size());
    Path top;
    for(int i=lo;i<end;i++){
        auto left=vertices(order[i]);Solver s(t,left,target);bool hit=s.solve();visits+=s.nodes;fits+=s.placements;conn+=s.connected;tried+=s.deep;capped+=s.limits;
        if(s.best.size()>top.size()){top=s.best;assert(valid(top));cout<<"BEST "<<int(top.size())-1;for(int x:top)cout<<" "<<x;cout<<endl;}
        if(hit){assert(valid(s.solution));cout<<"FOUND "<<i<<" "<<s.solution.size()-1;for(int x:s.solution)cout<<" "<<x;cout<<endl;return 0;}
        if(i%10==9)cout<<"AT "<<i+1<<" "<<end<<" "<<visits<<" "<<fits<<" "<<conn<<" "<<tried<<" "<<capped<<endl;
    }
    cout<<"DONE "<<lo<<" "<<end<<" "<<B.size()<<" "<<visits<<" "<<fits<<" "<<conn<<" "<<tried<<" "<<capped<<endl;
}

#endif
