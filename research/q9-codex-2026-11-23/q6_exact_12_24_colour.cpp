#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>

using Mask = std::uint32_t;
std::array<Mask,32> adj;
std::array<int,32> even,odd;
int target;
std::uint64_t supports=0, eligible_supports=0, search_nodes=0;
Mask witness_black=0,witness_white=0;

bool acyclic(Mask black,Mask white) {
    while (black) {
        Mask left = black & -black, right=0;
        for (;;) {
            Mask new_right=right, new_left=left;
            for (Mask rows=left;rows;rows&=rows-1)
                new_right |= adj[__builtin_ctz(rows)]&white;
            for (Mask rows=black&~left;rows;rows&=rows-1) {
                int u=__builtin_ctz(rows);
                if (adj[u]&new_right) new_left|=Mask(1)<<u;
            }
            if (new_left==left && new_right==right) break;
            left=new_left;
            right=new_right;
        }
        // All black vertices have degree two. The component is a cycle
        // exactly when the two parts have equal cardinality.
        if (__builtin_popcount(left)==__builtin_popcount(right)) return false;
        black &= ~left;
        white &= ~right;
    }
    return true;
}

bool choose_white(Mask black,Mask white) {
    ++search_nodes;
    if (__builtin_popcount(white)<target) return false;
    Mask branch=0;
    int excess=0;
    for (Mask rows=black;rows;rows&=rows-1) {
        Mask nb=adj[__builtin_ctz(rows)]&white;
        int d=__builtin_popcount(nb);
        if (d<2 || d-2>__builtin_popcount(white)-target) return false;
        if (d>2 && (excess==0 || d<excess)) branch=nb,excess=d;
    }
    if (!branch) {
        if (!acyclic(black,white)) return false;
        witness_black=black;
        witness_white=white;
        return true;
    }
    // Any feasible completion has to omit a neighbour of this black vertex.
    for (;branch;branch&=branch-1) {
        Mask cut=branch&-branch;
        if (choose_white(black,white&~cut)) return true;
    }
    return false;
}

bool enumerate(int first,int left,Mask chosen,Mask zero,Mask one,Mask two) {
    if (!left) {
        ++supports;
        if (__builtin_popcount(zero|one|two)<target ||
            __builtin_popcount(one)+2*__builtin_popcount(two)<24) return false;
        ++eligible_supports;
        return choose_white(chosen,zero|one|two);
    }
    for (int i=first;i<=32-left;++i) {
        Mask nb=adj[i];
        if (enumerate(i+1,left-1,chosen|(Mask(1)<<i),zero&~nb,
                      (one&~nb)|(zero&nb),(two&~nb)|(one&nb))) return true;
    }
    return false;
}

int main(int argc,char** argv) {
    if (argc!=2) return 2;
    target=std::atoi(argv[1]);
    if (target<12 || target>20) return 2;
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
    bool hit=enumerate(2,10,3,~(adj[0]|adj[1]),adj[0]^adj[1],adj[0]&adj[1]);
    std::printf("{\"target\":%d,\"status\":\"%s\",\"supports\":%llu,\"eligible_supports\":%llu,\"search_nodes\":%llu,\"points\":[",
                target,hit?"WITNESS":"EXHAUSTIVE_EXCLUSION",
                static_cast<unsigned long long>(supports),
                static_cast<unsigned long long>(eligible_supports),
                static_cast<unsigned long long>(search_nodes));
    bool first=true;
    for (int i=0;i<32;++i) {
        if (witness_black>>i&1) std::printf("%s%d",first?"":",",even[i]),first=false;
        if (witness_white>>i&1) std::printf("%s%d",first?"":",",odd[i]),first=false;
    }
    std::puts("]}");
}

