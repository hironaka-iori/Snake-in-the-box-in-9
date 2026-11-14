// Literal enumeration of all two-for-two exchanges to check the grouped pair filter.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using Mask = std::uint64_t;

int main() {
    std::array<bool,256> used{};
    int v;
    while (std::cin >> v) used.at(v)=true;
    std::vector<int> old,holes,candidates;
    std::array<int,256> degree{},parity{};
    int even=0;
    for (int x=0;x<256;++x) {
        (used[x]?old:holes).push_back(x);
        parity[x]=1-std::popcount(unsigned(x))%2;
        even+=used[x]*parity[x];
        for (int j=0;j<8;++j) degree[x]+=used[x^(1<<j)];
        if (degree[x]<=4) candidates.push_back(x);
    }
    if (old.size()!=191 || candidates.size()>63) return 1;
    std::array<Mask,256> adjacent{},site{};
    Mask initially_used=0;
    for (unsigned i=0;i<candidates.size();++i) {
        int x=candidates[i];site[x]=Mask(1)<<i;
        if (used[x]) initially_used|=site[x];
        for (int j=0;j<8;++j) adjacent[x^(1<<j)]|=site[x];
    }
    std::array<std::array<std::uint64_t,64>,64> counts{};
    for (unsigned i=0;i<old.size();++i) for (unsigned j=0;j<i;++j) {
        int x=old[i],y=old[j];used[x]=used[y]=false;
        Mask remaining=initially_used&~(site[x]|site[y]);
        std::array<Mask,3> deg{};
        for(int r:candidates) {
            int now=degree[r]-bool(adjacent[x]&site[r])-bool(adjacent[y]&site[r]);
            if(now<=2) deg[now]|=site[r];
        }
        for(unsigned a=0;a<holes.size();++a) for(unsigned b=0;b<a;++b) {
            int u=holes[a],w=holes[b],e=even-parity[x]-parity[y]+parity[u]+parity[w];
            if(e<95 || e>96) continue;
            Mask touched=adjacent[u]|adjacent[w],twice=adjacent[u]&adjacent[w];
            Mask valid=((deg[2]&~touched)|(deg[1]&~twice)|(deg[0]&touched))&(remaining|site[u]|site[w]);
            if(std::popcount(valid)<2) continue;
            used[u]=used[w]=true;
            for(Mask left=valid;left;) {
                int h=std::countr_zero(left);left&=left-1;
                for(Mask right=left;right;right&=right-1) {
                    int k=std::countr_zero(right),r=candidates[h],s=candidates[k];
                    unsigned diff=r^s;int distance=std::popcount(diff);
                    if(distance==1) continue;
                    if(distance==2 && (used[r^(diff&(-diff))] || used[s^(diff&(-diff))])) continue;
                    ++counts[h][k];
                }
            }
            used[u]=used[w]=false;
        }
        used[x]=used[y]=true;
    }
    for(unsigned i=0;i<candidates.size();++i) for(unsigned j=i+1;j<candidates.size();++j)
        if(counts[i][j]) std::cout << candidates[i] << ' ' << candidates[j] << ' ' << counts[i][j] << '\n';
}
