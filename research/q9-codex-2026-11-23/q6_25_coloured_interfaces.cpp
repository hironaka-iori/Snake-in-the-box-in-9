#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <vector>
using Bits=std::uint64_t;
using Key=std::array<int,6>;
struct Shape { Bits selected, interior; int components,black; };
std::array<Bits,64> adj{};
Bits black_mask=0;

int pop(Bits x) {return __builtin_popcountll(x);}
int low(Bits x) {return __builtin_ctzll(x);}
Bits bit(int i) {return Bits(1)<<i;}

Bits transform(Bits x,const std::array<int,64>& map,int shift) {
    Bits y=0;
    for (;x;x&=x-1) y|=bit(map[low(x)]^shift);
    return y;
}

Bits swap_colours(Bits x) {
    return ((x&0x5555555555555555ULL)<<1)|((x&0xaaaaaaaaaaaaaaaaULL)>>1);
}

bool is_forest(Bits a,Bits b) {
    std::array<Bits,2> todo{a,b};
    while (todo[0] || todo[1]) {
        const int layer=todo[0]?0:1;
        std::vector<std::pair<int,int>> stack{{layer,low(todo[layer])}};
        todo[layer]&=~bit(stack[0].second);
        bool all_two=true;
        while (!stack.empty()) {
            auto [s,v]=stack.back();
            stack.pop_back();
            Bits around=adj[v]&(s?b:a);
            bool cross=(bit(v)&(s?a:b))!=0;
            if (pop(around)+int(cross)!=2) all_two=false;
            for (Bits live=around&todo[s];live;live&=live-1)
                stack.push_back({s,low(live)});
            todo[s]&=~around;
            if (cross && (todo[1-s]&bit(v))) {
                todo[1-s]&=~bit(v);
                stack.push_back({1-s,v});
            }
        }
        if (all_two) return false;
    }
    return true;
}

int path_distance(Bits points,int a,int b) {
    Bits seen=bit(a), frontier=seen;
    for (int distance=0;frontier;++distance) {
        if (frontier&bit(b)) return distance;
        Bits next=0;
        for (Bits rows=frontier;rows;rows&=rows-1) next|=adj[low(rows)];
        frontier=next&points&~seen;
        seen|=frontier;
    }
    return -1;
}

int main(int argc,char** argv) {
    if (argc<2 || (argc>4 && argc!=8)) return 2;
    const bool requested=argc==8;
    const int target_edges=requested?std::atoi(argv[4]):25;
    const int first_components=requested?std::atoi(argv[5]):0;
    const int second_components=requested?std::atoi(argv[6]):0;
    const int requested_crossings=requested?std::atoi(argv[7]):0;
    for (int v=0;v<64;++v) {
        if (!(__builtin_popcount(static_cast<unsigned>(v))%2)) black_mask|=bit(v);
        for (int d=0;d<6;++d) adj[v]|=bit(v^(1<<d));
    }
    std::ifstream source(argv[1]);
    std::vector<Shape> bank;
    std::array<int,9> degrees{},observed{};
    for (std::string tag;source>>tag;) {
        int c;source>>c;
        if (c<1 || c>8) return 3;
        if (tag=="classes") {
            int count;source>>count;
            degrees[c]=count;
            continue;
        }
        if (tag!="representative") return 3;
        std::string string;source>>string;
        Bits points=std::stoull(string,nullptr,16), interior=0;
        int incidence=0;
        for (Bits rows=points;rows;rows&=rows-1) {
            int u=low(rows),d=pop(adj[u]&points);
            if (d>2) return 4;
            incidence+=d;
            if (d==2) interior|=bit(u);
        }
        if (incidence!=2*target_edges || pop(points)!=target_edges+c || !is_forest(points,0)) return 4;
        ++observed[c];
        bank.push_back({points,interior,c,pop(points&black_mask)});
    }
    if (observed!=degrees) return 5;
    if (!requested && (degrees[1]!=51 || degrees[2]!=102 || degrees[3]!=55 || bank.size()!=208)) return 5;
    std::uint64_t placements=0,degree_compatible=0;
    std::map<Key,std::array<Bits,2>> signatures;
    std::set<std::array<int,3>> double_geometry;
    std::set<std::array<int,2>> port_degrees;
    std::set<std::array<Bits,4>> placements_by_anchor;
    std::set<std::array<Bits,5>> exact_pairs;
    for (const Shape& b:bank) {
        if (requested && b.components!=second_components) continue;
        std::array<int,6> permutation{0,1,2,3,4,5};
        do {
            std::array<int,64> labels{};
            for (int u=1;u<64;++u) labels[u]=labels[u&(u-1)]|(1<<permutation[low(u)]);
            std::array<int,64> identity{};
            for (int u=0;u<64;++u) identity[u]=u;
            Bits p=transform(b.selected,labels,0),q=transform(b.interior,labels,0);
            for (int shift=0;shift<64;++shift) {
                Bits bp=transform(p,identity,shift),bi=transform(q,identity,shift);
                int b_black=pop(bp&black_mask);
                for (const Shape& a:bank) {
                    if (requested && a.components!=first_components) continue;
                    ++placements;
                    if ((a.interior&bp)||(bi&a.selected)) continue;
                    Bits intersection=a.selected&bp;
                    int rb=pop(intersection&black_mask),rw=pop(intersection&~black_mask);
                    if (rb+rw==0 || (requested && rb+rw!=requested_crossings)) continue;
                    ++degree_compatible;
                    const Key key{a.components,b.components,a.black,b_black,rb,rw};
                    if (rb+rw>1 && !is_forest(a.selected,bp)) continue;
                    if (rb+rw==2) {
                        int u=low(intersection),v=low(intersection&(intersection-1));
                        double_geometry.insert({pop(u^v),path_distance(a.selected,u,v),
                                                path_distance(bp,u,v)});
                    }
                    placements_by_anchor.insert({a.selected,static_cast<Bits>(b.components),
                                                 static_cast<Bits>(rb+rw),intersection});
                    for (Bits points=intersection;points;points&=points-1) {
                        const int u=low(points);
                        port_degrees.insert({pop(adj[u]&a.selected),pop(adj[u]&bp)});
                    }
                    if (argc>=4) exact_pairs.insert({a.selected,bp,static_cast<Bits>(a.components),
                                                    static_cast<Bits>(b.components),static_cast<Bits>(rb+rw)});
                    if (signatures.count(key)) continue;
                    signatures[key]={a.selected,bp};
                    const Key reflected{a.components,b.components,target_edges+a.components-a.black,
                                        target_edges+b.components-b_black,rw,rb};
                    signatures[reflected]={swap_colours(a.selected),swap_colours(bp)};
                }
            }
        } while (std::next_permutation(permutation.begin(),permutation.end()));
    }
    if (argc>=3) {
        std::FILE* archive=std::fopen(argv[2],"w");
        if (!archive) return 6;
        for (const auto& x:placements_by_anchor)
            std::fprintf(archive,"{\"anchor\":\"%016llx\",\"other_components\":%llu,\"crossings\":%llu,\"ports\":\"%016llx\"}\n",
                         (unsigned long long)x[0],(unsigned long long)x[1],
                         (unsigned long long)x[2],(unsigned long long)x[3]);
        std::fclose(archive);
        for (const auto& x:port_degrees)
            std::fprintf(stderr,"{\"local_port_degrees\":[%d,%d]}\n",x[0],x[1]);
    }
    if (argc>=4) {
        std::FILE* archive=std::fopen(argv[3],"w");
        if (!archive) return 6;
        for (const auto& x:exact_pairs) {
            std::fprintf(archive,"{\"masks\":[\"%016llx\",\"%016llx\"],\"components\":[%llu,%llu],\"crossings\":%llu",
                         (unsigned long long)x[0],(unsigned long long)x[1],
                         (unsigned long long)x[2],(unsigned long long)x[3],
                         (unsigned long long)x[4]);
            if (requested) std::fprintf(archive,",\"edges\":[%d,%d]",target_edges,target_edges);
            std::fputs("}\n",archive);
        }
        std::fclose(archive);
    }
    for (const auto& g:double_geometry)
        std::fprintf(stderr,"{\"port_distance\":%d,\"within_layers\":[%d,%d]}\n",g[0],g[1],g[2]);
    std::printf("{\"placements\":%llu,\"degree_compatible\":%llu,\"signatures\":%zu}\n",
                (unsigned long long)placements,(unsigned long long)degree_compatible,signatures.size());
    for (const auto& [key,masks]:signatures)
        std::printf("{\"key\":[%d,%d,%d,%d,%d,%d],\"masks\":[\"%016llx\",\"%016llx\"]}\n",
                    key[0],key[1],key[2],key[3],key[4],key[5],
                    (unsigned long long)masks[0],(unsigned long long)masks[1]);
}

