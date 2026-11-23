#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <map>
#include <set>
#include <vector>
using Bits = std::uint64_t;
struct Shape { Bits points, inner; };
std::array<Bits,64> adj;
std::array<std::set<Bits>,3> shapes;

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
void second_path(int v, Bits used, Bits available, int left, Bits anchor) {
    if (!left) {
        shapes[2].insert(canonical(anchor|used));
        return;
    }
    for (Bits walk=adj[v]&available&~used;walk;walk&=walk-1) {
        int w=first(walk);
        second_path(w,used|bit(w),available&~adj[v],left-1,anchor);
    }
}
void anchor_path(int v, Bits used, Bits available, int length, int max_axis) {
    if (length==27) {
        shapes[1].insert(canonical(used));
    }
    if (length>=14) {
        Bits pool=available&~adj[v]&~used;
        int needed=28-length;
        if (count(pool)>=needed)
            for (Bits walk=pool;walk;walk&=walk-1) {
                int w=first(walk);
                second_path(w,bit(w),pool,needed-1,used);
            }
    }
    if (length==27) return;
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
int main() {
    for (int v=0;v<64;++v) for (int d=0;d<6;++d) adj[v]|=bit(v^(1<<d));
    anchor_path(0,1,~Bits(0),1,-1);
    for (int k=1;k<=2;++k) {
        std::printf("classes %d %zu\n",k,shapes[k].size());
        for (auto mask:shapes[k]) std::printf("representative %d %016llx\n",k,(unsigned long long)mask);
    }
    for (int left=1;left<=2;++left) for (int right=left;right<=2;++right) {
        std::array<unsigned long long,5> hist{};
        for (auto b:shapes[right]) {
            auto B=describe(b);
            std::array<int,6> axes{0,1,2,3,4,5};
            do {
                std::array<int,64> image{};
                for (int v=1;v<64;++v) image[v]=image[v&(v-1)]|(1<<axes[__builtin_ctz(v)]);
                for (int t=0;t<64;++t) {
                    Shape translated{permute(B.points,image,t),permute(B.inner,image,t)};
                    for (auto a:shapes[left]) {
                        auto A=describe(a);
                        if ((A.inner&translated.points)||(translated.inner&A.points)) continue;
                        ++hist[count(A.points&translated.points)];
                    }
                }
            } while (std::next_permutation(axes.begin(),axes.end()));
        }
        std::printf("degree-compatible %d %d",left,right);
        for (auto value:hist) std::printf(" %llu",value);
        std::puts("");
    }
    return 0;
}
