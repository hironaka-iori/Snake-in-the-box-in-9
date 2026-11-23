#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <map>
#include <set>
#include <vector>
using Bits = std::uint64_t;
struct Shape { Bits points, inner; };
std::array<Bits,64> adj;
std::array<std::set<Bits>,9> shapes;
int target_edges = 25;
int minimum_components = 1;
int maximum_components = 3;

Bits bit(int v) { return Bits(1)<<v; }
int count(Bits m) { return __builtin_popcountll(m); }
int first(Bits m) { return __builtin_ctzll(m); }
Bits permute(Bits points, const std::array<int,64>& image, int origin) {
    Bits result=0;
    for (Bits walk=points;walk;walk&=walk-1) result|=bit(image[first(walk)]^origin);
    return result;
}
Bits canonical(Bits points) {
    Bits best=~Bits(0);
    for (Bits ends=points;ends;ends&=ends-1) {
        int start=first(ends);
        if (count(adj[start]&points)!=1) continue;
        std::vector<int> axes, remaining;
        int prev=-1, v=start;
        while (true) {
            Bits forward=adj[v]&points;
            if (prev>=0) forward&=~bit(prev);
            if (!forward) break;
            int w=first(forward), d=__builtin_ctz(v^w);
            if (std::find(axes.begin(),axes.end(),d)==axes.end()) axes.push_back(d);
            prev=v; v=w;
        }
        for (int d=0;d<6;++d)
            if (std::find(axes.begin(),axes.end(),d)==axes.end()) remaining.push_back(d);
        do {
            auto order=axes;
            order.insert(order.end(),remaining.begin(),remaining.end());
            std::array<int,64> image{};
            for (int w=0;w<64;++w)
                for (int i=0;i<6;++i) if ((w^start)&(1<<order[i])) image[w]|=1<<i;
            best=std::min(best,permute(points,image,0));
        } while (std::next_permutation(remaining.begin(),remaining.end()));
    }
    return best;
}
void add_paths(Bits occupied, Bits available, int vertices, int components,
               int largest, int original_components);

void extend_piece(int v, Bits piece, Bits available, int steps, Bits occupied,
                  int vertices, int components, int largest, int original_components) {
    if (steps==0) {
        add_paths(occupied|piece,available&~adj[v]&~piece,vertices,components,
                  largest,original_components);
        return;
    }
    for (Bits walk=adj[v]&available&~piece; walk;walk&=walk-1) {
        int next=first(walk);
        extend_piece(next,piece|bit(next),available&~adj[v],steps-1,occupied,
                     vertices,components,largest,original_components);
    }
}

void add_paths(Bits occupied, Bits available, int vertices, int components,
               int largest, int original_components) {
    if (components==0) {
        if (vertices==0) shapes[original_components].insert(canonical(occupied));
        return;
    }
    if (count(available)<vertices || largest*components<vertices) return;
    for (int n=(vertices+components-1)/components;
         n<=std::min(largest,vertices-components+1); ++n)
        for (Bits walk=available;walk;walk&=walk-1) {
            int v=first(walk);
            extend_piece(v,bit(v),available,n-1,occupied,vertices-n,components-1,
                         n,original_components);
        }
}

void anchor_path(int v, Bits used, Bits available, int length, int max_axis) {
    for (int c=minimum_components;c<=maximum_components;++c) {
        int needed=target_edges+c-length;
        if (needed>=c-1 && needed<=(c-1)*length)
            add_paths(used,available&~adj[v]&~used,needed,c-1,length,c);
    }
    if (length==target_edges+1) return;
    for (Bits walk=adj[v]&available&~used;walk;walk&=walk-1) {
        int w=first(walk), axis=__builtin_ctz(v^w);
        if (axis<=max_axis+1)
            anchor_path(w,used|bit(w),available&~adj[v],length+1,std::max(max_axis,axis));
    }
}
Shape describe(Bits points) {
    Shape result{points,0};
    for (Bits walk=points;walk;walk&=walk-1) {
        int v=first(walk);
        if (count(points&adj[v])==2) result.inner|=bit(v);
    }
    return result;
}
int main(int argc, char** argv) {
    if (argc!=1 && argc!=4) return 2;
    if (argc==4) {
        target_edges=std::atoi(argv[1]);
        minimum_components=std::atoi(argv[2]);
        maximum_components=std::atoi(argv[3]);
        if (target_edges<22 || target_edges>26 || minimum_components<1 ||
            maximum_components>8 || minimum_components>maximum_components) return 2;
    }
    for (int v=0;v<64;++v) for (int d=0;d<6;++d) adj[v]|=bit(v^(1<<d));
    anchor_path(0,1,~Bits(0),1,-1);
    for (int k=minimum_components;k<=maximum_components;++k) {
        std::printf("classes %d %zu\n",k,shapes[k].size());
        for (auto mask:shapes[k]) std::printf("representative %d %016llx\n",k,(unsigned long long)mask);
    }
}
