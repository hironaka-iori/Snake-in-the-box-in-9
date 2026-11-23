#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>

struct Forest {
    uint32_t points, inner;
    int population, edges;
};

std::array<uint64_t,64> adjacency{};

bool describe(uint64_t mask, Forest& shape) {
    uint64_t inner=0, reached=0;
    int degrees=0;
    for (uint64_t scan=mask; scan; scan&=scan-1) {
        int v=std::countr_zero(scan);
        int degree=std::popcount(mask&adjacency[v]);
        if (degree>2) return false;
        degrees+=degree;
        if (degree==2) inner|=uint64_t(1)<<v;
        else reached|=uint64_t(1)<<v;
    }
    for (uint64_t pending=reached; pending;) {
        int v=std::countr_zero(pending);
        pending&=pending-1;
        uint64_t next=adjacency[v]&mask&~reached;
        pending|=next;
        reached|=next;
    }
    if (reached!=mask) return false;
    assert(degrees%2==0);
    shape={uint32_t(mask),uint32_t(inner),std::popcount(mask),degrees/2};
    return true;
}

void make_adjacency(int dim) {
    adjacency.fill(0);
    for (int v=0;v<(1<<dim);++v)
        for (int axis=0;axis<dim;++axis)
            adjacency[v]|=uint64_t(1)<<(v^(1<<axis));
}

using ByteMap=std::array<std::array<uint32_t,256>,4>;

std::vector<ByteMap> coordinate_permutations() {
    std::array<int,5> order{0,1,2,3,4};
    std::vector<ByteMap> tables;
    do {
        ByteMap map{};
        for (int byte=0;byte<4;++byte)
            for (int bits=1;bits<256;++bits) {
                int vertex=8*byte+std::countr_zero(unsigned(bits));
                int image=0;
                for (int i=0;i<5;++i)
                    if (vertex&(1<<i)) image|=1<<order[i];
                map[byte][bits]=map[byte][bits&(bits-1)] | (uint32_t(1)<<image);
            }
        tables.push_back(map);
    } while (std::next_permutation(order.begin(),order.end()));
    return tables;
}

uint32_t translated(uint32_t mask,int origin) {
    constexpr std::array<uint32_t,5> low{0x55555555U,0x33333333U,0x0f0f0f0fU,0x00ff00ffU,0x0000ffffU};
    for (int i=0;i<5;++i)
        if (origin&(1<<i))
            mask=((mask&low[i])<<(1<<i)) | ((mask&~low[i])>>(1<<i));
    return mask;
}

int main() {
    make_adjacency(4);
    std::vector<Forest> four;
    for (unsigned mask=0;mask<(1u<<16);++mask) {
        Forest forest{};
        if (describe(mask,forest)) {
            assert(forest.population<=8);
            four.push_back(forest);
        }
    }
    assert(four.size()==14911);
    std::cout<<"q4_forests "<<four.size()<<std::endl;

    make_adjacency(5);
    std::array<std::vector<Forest>,14> labelled, representatives;
    for (const auto& a:four)
        for (const auto& b:four) {
            uint32_t common=a.points&b.points;
            if (common&(a.inner|b.inner)) continue;
            int edges=a.edges+b.edges+std::popcount(common);
            if (edges<8 || a.population+b.population<11) continue;
            Forest forest{};
            if (!describe(a.points|(uint64_t(b.points)<<16),forest)) continue;
            assert(forest.edges==edges && edges<=13);
            labelled[edges].push_back(forest);
        }

    auto maps=coordinate_permutations();
    for (int edges=8;edges<=13;++edges) {
        std::unordered_set<uint32_t> orbit;
        for (const auto& forest:labelled[edges]) {
            if (orbit.contains(forest.points)) continue;
            representatives[edges].push_back(forest);
            for (const auto& map:maps) {
                uint32_t image=0;
                for (int i=0;i<4;++i) image|=map[i][(forest.points>>(8*i))&255];
                for (int origin=0;origin<32;++origin)
                    orbit.insert(translated(image,origin));
            }
        }
        assert(orbit.size()==labelled[edges].size());
        std::cout<<"q5_edges "<<edges<<" labelled "<<labelled[edges].size()
                 <<" orbits "<<representatives[edges].size()<<std::endl;
    }

    make_adjacency(6);
    for (auto [edges,minimum]:std::array<std::pair<int,int>,4>{{{26,0},{27,0},{25,29},{26,29}}}) {
        bool found=false;
        uint64_t mask=0, tested=0;
        for (int r=0;r<=edges/6 && !found;++r)
            for (int first=13;first>=8 && !found;--first) {
                int second=edges-r-first;
                if (second<8 || second>first) continue;
                for (const auto& a:representatives[first]) {
                    if (found) break;
                    for (const auto& b:labelled[second]) {
                        ++tested;
                        if (a.population+b.population<minimum) continue;
                        uint32_t shared=a.points&b.points;
                        if ((shared&(a.inner|b.inner)) || std::popcount(shared)!=r) continue;
                        Forest forest{};
                        uint64_t candidate=a.points|(uint64_t(b.points)<<32);
                        if (!describe(candidate,forest)) continue;
                        assert(forest.edges==edges);
                        found=true;
                        mask=candidate;
                        break;
                    }
                }
            }
        std::cout<<"edge_target "<<edges<<" minimum_population "<<minimum
                 <<" tested "<<tested<<" found "<<found<<" witness "<<std::hex<<mask<<std::dec<<std::endl;
        if (edges==26 && minimum==0) assert(found);
    }
}
