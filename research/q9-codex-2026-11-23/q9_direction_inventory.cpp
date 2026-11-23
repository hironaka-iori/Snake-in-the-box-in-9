#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

struct Pattern {
    int sum;
    std::vector<std::pair<int,int>> multiplicity;
};
std::vector<Pattern> forbidden;
std::array<int,75> histogram{};
std::array<int,9> chosen{};
std::array<std::array<std::uint64_t,74>,10> baseline{},admissible{};

bool is_forbidden() {
    for (const auto& pattern:forbidden) {
        bool present=true;
        for (const auto& [value,n]:pattern.multiplicity) {
            if (histogram[value]<n) {
                present=false;
                break;
            }
        }
        if (present) return true;
    }
    return false;
}

void enumerate(int i,int total,int odd,int previous) {
    if (i==9) {
        if (total!=0 || odd<3 || odd%2==0) return;
        const int smallest=chosen[0]+chosen[1]+chosen[2];
        ++baseline[odd][smallest];
        if (!is_forbidden()) ++admissible[odd][smallest];
        return;
    }
    int lb=std::max(previous,total-74*(8-i));
    if (i==1) lb=std::max(lb,17-chosen[0]);
    int ub=std::min(74,total/(9-i));
    if (i==8) lb=ub=total;
    for (int v=lb;v<=ub;++v) {
        if (v<previous || v>74) continue;
        chosen[i]=v;
        ++histogram[v];
        enumerate(i+1,total-v,odd+v%2,v);
        --histogram[v];
    }
}

int main() {
    for (std::array<int,3> values; std::cin>>values[0]>>values[1]>>values[2];) {
        std::sort(values.begin(),values.end());
        Pattern p{values[0]+values[1]+values[2],{}};
        for (int v:values) {
            if (v<3 || v>74) return 2;
            if (!p.multiplicity.empty() && p.multiplicity.back().first==v)
                ++p.multiplicity.back().second;
            else p.multiplicity.push_back({v,1});
        }
        forbidden.push_back(p);
    }
    enumerate(0,221,0,3);
    for (int d=3;d<=9;d+=2)
        for (int sum=26;sum<=73;++sum)
            if (baseline[d][sum])
                std::cout<<d<<' '<<sum<<' '<<baseline[d][sum]<<' '<<admissible[d][sum]<<'\n';
}

