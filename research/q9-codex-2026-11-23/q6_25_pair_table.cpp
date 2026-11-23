#define main previous_main
#include "q6_26_edge_interfaces.cpp"
#undef main
#include <fstream>
#include <string>

bool acyclic(Bits a, Bits b) {
    Bits remaining[2]={a,b};
    while (remaining[0] || remaining[1]) {
        int origin=remaining[0]?0:1;
        std::vector<int> work{64*origin+first(remaining[origin])};
        remaining[origin]&=~bit(work.front()%64);
        int edges=0;
        for (std::size_t i=0;i<work.size();++i) {
            int v=work[i]%64, side=work[i]/64;
            Bits available=(side?b:a)&adj[v];
            edges+=count(available)+(((side?a:b)&bit(v))!=0);
            for (Bits more=available&remaining[side];more;more&=more-1) {
                int w=first(more);work.push_back(64*side+w);
                remaining[side]&=~bit(w);
            }
            if (remaining[1-side]&bit(v)) {
                work.push_back(64*(1-side)+v);
                remaining[1-side]&=~bit(v);
            }
        }
        if (edges!=2*(int(work.size())-1)) return false;
    }
    return true;
}

int main(int argc,char** argv) {
    if (argc!=2) return 1;
    for (int v=0;v<64;++v) for (int d=0;d<6;++d) adj[v]|=bit(v^(1<<d));
    std::ifstream source(argv[1]);
    std::vector<Shape> shapes25;
    std::string token, mask;
    int c;
    while (source>>token>>c>>mask) {
        if (token=="representative") shapes25.push_back(describe(std::stoull(mask,nullptr,16)));
    }
    if (shapes25.size()!=28) return 2;
    std::array<std::array<std::array<unsigned long long,7>,4>,4> histogram{};
    for (auto B:shapes25) {
        std::array<int,6> axes{0,1,2,3,4,5};
        do {
            std::array<int,64> image{};
            for (int v=1;v<64;++v) image[v]=image[v&(v-1)]|(1<<axes[__builtin_ctz(v)]);
            for (int t=0;t<64;++t) {
                Bits points=permute(B.points,image,t), inner=permute(B.inner,image,t);
                for (auto A:shapes25) {
                    int r=count(A.points&points);
                    if (!r || (A.inner&points) || (inner&A.points) || !acyclic(A.points,points)) continue;
                    ++histogram[count(A.points)-25][count(points)-25][r];
                }
            }
        } while (std::next_permutation(axes.begin(),axes.end()));
    }
    for (int c1=1;c1<=3;++c1) for (int c2=1;c2<=3;++c2)
        for (int r=1;r<=6;++r) if (histogram[c1][c2][r])
            std::printf("components %d %d contacts %d placements %llu\n",c1,c2,r,histogram[c1][c2][r]);
}
