#define Q9_TREE_LIBRARY
#include "tree.cpp"
#include <numeric>
array<uint8_t,9> canon(const Tree& t){
    int a=countr_zero(unsigned(t.masks[0]));int b=countr_zero(unsigned(t.masks[0]^(1<<a)));
    int e1=countr_zero(unsigned(t.masks[1]));
    int root=((t.off[a]^t.off[e1])&1)?b:a;
    auto x=t.off;for(auto& z:x)z^=t.off[root];sort(x.begin(),x.end());return x;
}
int main(){
    Edges e{};e[0]={0,1};e[1]={1,2};grow(e,3);
    vector<array<uint8_t,9>> ours,other;
    for(auto& t:trees)ours.push_back(canon(t));
    // Decode all vertex-labeled Prüfer words with fixed edge 0--1;
    // orient the residual forest toward these roots and name every edge by its child.
    int total=1;for(int i=0;i<7;i++)total*=9;
    for(int word=0;word<total;word++){
        int q=word;array<int,7> code;array<int,9> deg,adj{};deg.fill(1);
        for(auto& x:code){x=q%9;q/=9;++deg[x];}
        auto link=[&](int a,int b){adj[a]|=1<<b;adj[b]|=1<<a;};
        for(int x:code){int a=0;while(deg[a]!=1)a++;link(a,x);deg[a]=0;--deg[x];}
        int ends=0;for(int i=0;i<9;i++)if(deg[i])ends|=1<<i;
        link(countr_zero(unsigned(ends)),bit_width(unsigned(ends))-1);
        if(!(adj[0]&2))continue;
        array<uint8_t,9> potentials{};potentials[1]=1;int seen=3;array<int,9> queue{0,1};int n=2;
        for(int i=0;i<n;i++){int v=queue[i];for(int free=adj[v]&~seen;free;free&=free-1){
            int child=countr_zero(unsigned(free));seen|=1<<child;queue[n++]=child;potentials[child]=potentials[v]^(1<<(child-1));
        }}
        if(potentials[2]&1)continue;
        sort(potentials.begin(),potentials.end());other.push_back(potentials);
    }
    sort(ours.begin(),ours.end());sort(other.begin(),other.end());
    assert(ours==other&&ours.size()==531441&&adjacent_find(ours.begin(),ours.end())==ours.end());
    cout<<"Prufer comparison "<<total<<" codes "<<ours.size()<<" distinct equal rooted potential sets"<<endl;
    string w;int rows=0;uint64_t verified=0;
    while(cin>>w){
        Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));Donor u(p);
        for(int i=(rows*247)%401;i<int(trees.size());i+=401){
            const auto& t=trees[i];array<uint8_t,512> load{};for(int v:p){int x=image(v,t);for(int d=0;d<9;d++)++load[x^(1<<d)];}
            assert(u.pairs(t)==count(load.begin(),load.end(),2));
            verified++;
        }rows++;
    }
    cout<<"independent original Q9 neighbor counts "<<verified<<" donors "<<rows<<endl;
}
