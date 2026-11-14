// Exact longest induced path from a fixed root, optionally to a prescribed tip,
// in an explicit Q7 subgraph. A component and bipartition bound prunes prefixes.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
struct Mask{uint64_t a=0,b=0;};
Mask operator|(Mask x,Mask y){return {x.a|y.a,x.b|y.b};}
Mask operator&(Mask x,Mask y){return {x.a&y.a,x.b&y.b};}
Mask minusset(Mask x,Mask y){return {x.a&~y.a,x.b&~y.b};}
Mask node(int v){return v<64?Mask{1ull<<v,0}:Mask{0,1ull<<(v-64)};}
int weight(Mask m){return popcount(m.a)+popcount(m.b);}
bool empty(Mask m){return !(m.a|m.b);}
bool has(Mask m,int v){return !empty(m&node(v));}
int take(Mask&m){if(m.a){int b=countr_zero(m.a);m.a&=m.a-1;return b;}int b=countr_zero(m.b);m.b&=m.b-1;return 64+b;}
array<Mask,128> adjacent{};
Mask even{};
struct Search{
    int tip,best=0,target;uint64_t nodes=0,limit;bool exhausted=true;
    vector<int> current,answer;
    int cap(Mask verts,int head){
        Mask seen=node(head),front=seen;
        while(!empty(front)){
            Mask next{};while(!empty(front))next=next|adjacent[take(front)];
            front=minusset(next&verts,seen);seen=seen|front;
        }
        if(tip>=0&&!has(seen,tip))return 0;
        int e=weight(even&seen),o=weight(seen)-e;
        if((popcount(unsigned(head))&1)==0)swap(e,o);
        if(tip>=0)return (popcount(unsigned(head^tip))&1)?2*min(e,o):2*min(e,o-1)+1;
        return min(2*o,2*e+1);
    }
    bool explore(int at,Mask allowed){
        if(++nodes>limit){exhausted=false;return true;}
        if((tip<0||at==tip)&&int(current.size())>best){best=int(current.size());answer=current;}
        if(best>=target)return true;
        if(tip>=0&&at==tip)return false;
        int depth=int(current.size());
        if(depth+weight(allowed)<=best)return false;
        if(depth-1+cap(allowed|node(at),at)<=best)return false;
        Mask choices=allowed&adjacent[at],next=minusset(allowed,adjacent[at]);
        if(tip>=0 && has(choices,tip))choices=node(tip);
        // If the fixed tip is adjacent, taking any other step makes that
        // adjacency a permanent chord and can never finish at the tip.
        while(!empty(choices)){
            int v=take(choices);current.push_back(v);
            if(explore(v,next))return true;current.pop_back();
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=3)return 2;
    for(int v=0;v<128;++v){
        if(!(popcount(unsigned(v))&1))even=even|node(v);
        for(int b=0;b<7;++b)adjacent[v]=adjacent[v]|node(v^(1<<b));
    }
    int root,tip,n;
    while(cin>>root>>tip>>n){
        Mask domain{};for(int i=0;i<n;++i){int v;cin>>v;domain=domain|node(v);}
        if(!has(domain,root)||(tip>=0&&!has(domain,tip)))return 3;
        Search s;s.tip=tip;s.target=stoi(argv[2]);s.limit=strtoull(argv[1],nullptr,10);
        s.current={root};s.explore(root,minusset(domain,node(root)));
        cout<<s.best<<" "<<s.nodes<<" "<<(s.exhausted&&s.best<s.target);
        for(int v:s.answer)cout<<" "<<v;cout<<"\n";
    }
}
