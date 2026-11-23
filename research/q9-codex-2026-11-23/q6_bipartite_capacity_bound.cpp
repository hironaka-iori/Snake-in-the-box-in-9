#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>

using Mask = std::uint32_t;
std::array<Mask, 32> adj;
std::array<int, 3> upper{};
std::uint64_t visited = 0;
int minority;

// For a fixed minority colour, zero/one/two hold the opposite-colour
// vertices with exactly that number of selected neighbours.
void finish(Mask chosen, Mask zero, Mask one, Mask two) {
    ++visited;
    const int n0 = __builtin_popcount(zero);
    const int n1 = __builtin_popcount(one);
    const int n2 = __builtin_popcount(two);
    const int available = n0+n1+n2;
    if (n1+2*n2 < 22 || available <= *std::min_element(upper.begin(),upper.end())) return;
    const Mask eligible = zero|one|two;
    int black_capacity = 0;
    for (Mask rows=chosen; rows; rows&=rows-1) {
        const int index = __builtin_ctz(rows);
        black_capacity += std::min(2,__builtin_popcount(adj[index]&eligible));
    }
    for (int e=22; e<=24; ++e) {
        if (e>2*minority || e>black_capacity) continue;
        for (int w=std::min(available,32-minority); w>upper[e-22] && w>=minority; --w) {
            int forced = std::max(0,w-n0);
            const int min_edges = std::min(n1,forced)+2*std::max(0,forced-n1);
            forced = std::max(0,w-n2);
            const int max_edges = 2*std::min(n2,w)+std::min(n1,forced);
            if (min_edges<=e && e<=max_edges) {
                upper[e-22] = w;
                break;
            }
        }
    }
}

void enumerate(int first, int left, Mask chosen, Mask zero, Mask one, Mask two) {
    if (left==0) {
        finish(chosen,zero,one,two);
        return;
    }
    for (int i=first; i<=32-left; ++i) {
        const Mask nb = adj[i];
        enumerate(i+1,left-1,chosen|(Mask(1)<<i),zero&~nb,
                  (one&~nb)|(zero&nb),(two&~nb)|(one&nb));
    }
}

int main(int argc,char** argv) {
    if (argc!=2) return 2;
    minority=std::atoi(argv[1]);
    if (minority<10 || minority>16) return 2;
    std::array<int,32> even{}, odd{};
    int a=0,b=0;
    for (int u=0;u<64;++u) {
        if (__builtin_parity(static_cast<unsigned>(u))) odd[b++]=u;
        else even[a++]=u;
    }
    if (even[0]!=0 || even[1]!=3) return 3;
    for (int u=0;u<32;++u)
        for (int v=0;v<32;++v)
            if (__builtin_popcount(static_cast<unsigned>(even[u]^odd[v]))==1)
                adj[u]|=Mask(1)<<v;
    // If all pair distances were at least four, the disjoint radius-one
    // balls would demand 7*minority > 64 vertices. Translate and permute
    // a distance-two pair to vertices 0 and 3.
    enumerate(2,minority-2,3,~(adj[0]|adj[1]),adj[0]^adj[1],adj[0]&adj[1]);
    std::printf("{\"minority\":%d,\"supports\":%llu,\"majority_upper_22_23_24\":[%d,%d,%d]}\n",
                minority,static_cast<unsigned long long>(visited),upper[0],upper[1],upper[2]);
}

