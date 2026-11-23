#define Q9_REM_LIBRARY
#include "remove.cpp"
#include <random>
#include <numeric>
struct Quiet:streambuf{int overflow(int c)override{return c;}};
uint64_t census(const Path& nodes,int r,int extra){
    uint64_t count=0;
    auto go=[&](auto&& self,int st,int budget,uint64_t dead)->void{
        if(budget){for(int i=st;i+budget<=int(nodes.size());i++)self(self,i+1,budget-1,dead|(uint64_t(1)<<i));return;}
        array<Path,512> adj;Path parents(nodes.size()),degree(nodes.size());iota(parents.begin(),parents.end(),0);
        auto root=[&](int v){while(parents[v]!=v)v=parents[v];return v;};
        int edges=0,cc=nodes.size()-r;
        for(int i=0;i<int(nodes.size());i++)if(!(dead>>i&1))
            for(int j=0;j<512;j++)if(popcount(unsigned(nodes[i]^j))==1)adj[j].push_back(i);
        for(auto& a:adj)if(a.size()==2){auto u=a[0],v=a[1];edges++;degree[u]++;degree[v]++;
            if(root(u)!=root(v)){cc--;parents[root(u)]=root(v);}}
        int deficit=0;for(int i=0;i<int(nodes.size());i++)if(!(dead>>i&1))deficit+=max(0,2-degree[i]);
        count+=edges>=int(nodes.size())-r-extra-1&&deficit<=2*extra+2&&cc<=extra+1;
    };
    go(go,0,r,0);return count;
}
int main(){
 Edges e{};e[0]={0,1};e[1]={1,2};grow(e,3);mt19937 rng(877511);
 string w;int num=0;uint64_t pos=0,neg=0;Quiet quiet;auto output=cout.rdbuf();
 while(cin>>w&&num<220){
    Path full{0};for(char c:w)full.push_back(full.back()^(1<<(c-'0')));
    int len=9+rng()%8,k=rng()%4,extra=rng()%4;Path cells,actual;
    const Tree& t=trees[rng()%trees.size()];array<int,512> inv;inv.fill(-1);
    for(int v=0;v<256;v++)inv[image(v,t)]=v;
    for(int i=0;i<len;i++){int q=full[2*i];cells.push_back(inv[q]);actual.push_back(q);}
    if(num%2){int ix=rng()%len,v;do{v=rng()%256;}while(find(cells.begin(),cells.end(),v)!=cells.end());cells[ix]=v;actual[ix]=image(v,t);}
    Donor donor(cells);maxEven=len-k+extra;keepCap=1;cout.rdbuf(&quiet);
    Rem rr(donor,t,k,donor.pairs(t),true);rr.dfs(0,k);
    cout.rdbuf(output);auto expected=census(actual,k,extra);
    assert(rr.finals==expected);pos+=expected>0;neg+=expected==0;num++;
 }
 cout<<"subset pruning reference "<<num<<" positive "<<pos<<" negative "<<neg<<endl;
}
