#include <algorithm>
#include <array>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <map>
#include <set>
#include <tuple>
#include <vector>

using Mask=std::uint64_t;
using Signature=std::array<int,5>;

Mask move(Mask mask,const std::array<int,64>& perm,int translation) {
    Mask result=0;
    while (mask) {
        auto v=__builtin_ctzll(mask);
        result|=Mask(1)<<(perm[v]^translation);
        mask&=mask-1;
    }
    return result;
}

int main() {
    std::map<std::pair<Signature,Mask>,std::set<Mask>> groups;
    for (Signature key;std::cin>>key[0]>>key[1]>>key[2]>>key[3]>>key[4];) {
        Mask a,b;
        if (!(std::cin>>std::hex>>a>>b>>std::dec) || !a || !b) return 2;
        groups[{key,a}].insert(b);
    }
    std::size_t original=0,canonical_count=0;
    for (const auto& [item,layouts]:groups) {
        const auto& [key,anchor]=item;
        original+=layouts.size();
        std::set<Mask> remaining=layouts;
        const int origin=__builtin_ctzll(anchor);
        std::vector<std::pair<std::array<int,64>,int>> stabilizer;
        std::array<int,6> axes{0,1,2,3,4,5};
        do {
            std::array<int,64> labels{};
            for (int u=1;u<64;++u) labels[u]=labels[u&(u-1)]|(1<<axes[__builtin_ctz(u)]);
            for (Mask possible=anchor;possible;possible&=possible-1) {
                const int shift=labels[origin]^__builtin_ctzll(possible);
                if (move(anchor,labels,shift)==anchor) stabilizer.push_back({labels,shift});
            }
        } while (std::next_permutation(axes.begin(),axes.end()));
        if (stabilizer.empty()) return 3;
        while (!remaining.empty()) {
            const auto representative=*remaining.begin();
            for (const auto& [labels,shift]:stabilizer) {
                const auto image=move(representative,labels,shift);
                if (!layouts.count(image)) return 4;
                remaining.erase(image);
            }
            ++canonical_count;
            std::cout<<key[0]<<' '<<key[1]<<' '<<key[2]<<' '<<key[3]<<' '<<key[4]<<' '
                     <<std::hex<<std::setw(16)<<std::setfill('0')<<anchor<<' '
                     <<std::setw(16)<<representative<<std::dec<<'\n';
        }
    }
    std::cerr<<"layouts "<<original<<" representatives "<<canonical_count<<'\n';
}

