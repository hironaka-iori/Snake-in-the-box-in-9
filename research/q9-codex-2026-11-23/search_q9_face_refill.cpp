// Exhaustively replace the selected vertices in one coordinate face of Q9.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using Bits = uint64_t;
struct Refill {
    std::array<bool,512> fixed{};
    std::array<int,512> degree{};
    std::array<int,64> label{}, external{};
    std::array<Bits,64> neighbors{};
    Bits pool=0;
    int fixed_edges=0, target=192;
    uint64_t leaves=0;
    std::vector<int> witness;
    bool connected(Bits selected) {
        auto occupied=fixed;
        while(selected){
            int i=std::countr_zero(selected); selected&=selected-1;
            occupied[label[i]]=true;
        }
        int head=-1, ends=0;
        for(int v=0;v<512;v++) if(occupied[v]){
            int d=0;
            for(int i=0;i<9;i++) d+=occupied[v^(1<<i)];
            if(d==1){head=v;ends++;}
            else if(d!=2) return false;
        }
        if(ends!=2)return false;
        int prev=-1;
        std::vector<int> path;
        while(head>=0){
            path.push_back(head);int next=-1;
            for(int d=0;d<9;d++){int u=head^(1<<d);if(occupied[u]&&u!=prev)next=u;}
            prev=head;head=next;
        }
        if(int(path.size())!=target+1)return false;
        witness=path;return true;
    }
    bool dfs(Bits choices,Bits selected,int need,int edge_count) {
        if(need==0){
            leaves++;
            return edge_count==target && connected(selected);
        }
        while(std::popcount(choices)>=need){
            int i=std::countr_zero(choices);Bits bit=Bits(1)<<i;choices^=bit;
            Bits adj=neighbors[i]&selected;
            int d=external[i]+std::popcount(adj);
            if(d>2)continue;
            bool overfull=false;
            for(Bits a=adj;a;a&=a-1){
                int j=std::countr_zero(a);
                if(external[j]+std::popcount(neighbors[j]&selected)>=2){overfull=true;break;}
            }
            if(overfull)continue;
            Bits next=d==2 ? choices&~neighbors[i] : choices;
            if(dfs(next,selected|bit,need-1,edge_count+d))return true;
        }
        return false;
    }
    bool solve(const std::vector<int>& p,int free_axes,int base){
        int need=target+1-static_cast<int>(p.size());
        for(int v:p){
            if((v&~free_axes)==base)need++;
            else fixed[v]=true;
        }
        for(int v:p)if(fixed[v]){
            for(int d=0;d<9;d++)degree[v]+=fixed[v^(1<<d)];
            fixed_edges+=degree[v];
        }
        fixed_edges/=2;
        std::array<int,9> axes{};int n=0;
        for(int d=0;d<9;d++)if(free_axes&(1<<d))axes[n++]=d;
        for(int i=0;i<(1<<n);i++){
            int v=base;
            for(int j=0;j<n;j++)if(i&(1<<j))v|=1<<axes[j];
            label[i]=v;bool admissible=true;
            for(int d=0;d<9;d++){
                int u=v^(1<<d);
                if(fixed[u]){external[i]++;if(degree[u]>=2)admissible=false;}
            }
            for(int j=0;j<n;j++)neighbors[i]|=Bits(1)<<(i^(1<<j));
            if(admissible && external[i]<=2)pool|=Bits(1)<<i;
        }
        return dfs(pool,0,need,fixed_edges);
    }
};
int main(int argc,char**argv){
    int dim=argc>1?std::atoi(argv[1]):5,target=argc>2?std::atoi(argv[2]):192;
    if(dim<1||dim>6||target<191||target>196)return 2;
    uint64_t cases=0,leaves=0;int rows=0;
    const int seed_edges=argc>3?std::atoi(argv[3]):191;
    if(seed_edges<1 || seed_edges>target) return 2;
    std::vector<int>p(seed_edges+1);
    while(std::cin>>p[0]){
        for(int i=1;i<=seed_edges;i++)if(!(std::cin>>p[i]))return 3;
        for(int i=0;i<=seed_edges;i++){
            if(p[i]<0||p[i]>=512)return 4;
            for(int j=0;j<i;j++){
                int d=std::popcount(unsigned(p[i]^p[j]));
                if(!d || (d==1)!=(i==j+1))return 4;
            }
        }
        rows++;
        for(int mask=1;mask<512;mask++)if(std::popcount(unsigned(mask))==dim){
            for(int base=0;base<512;base++)if(!(base&mask)){
                Refill f;f.target=target;cases++;
                if(f.solve(p,mask,base)){
                    std::cout<<"FOUND ";for(int x:f.witness)std::cout<<x<<" ";
                    std::cout<<"\n";return 0;
                }
                leaves+=f.leaves;
            }
        }
    }
    std::cout<<"rows "<<rows<<" faces "<<cases<<" tested subsets "<<leaves<<" no hit\n";
}
