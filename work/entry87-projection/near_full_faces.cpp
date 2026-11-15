// Exact minimum component count for a half-full or one-short seven-face.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>
using U=std::uint64_t;
std::array<U,6> lo;
U flip(U x,int i){int k=1<<i;return ((x&lo[i])<<k)|((x&~lo[i])>>k);}
U swap_axes(U x,int i,int j){
    U a=lo[i]&~lo[j],b=~lo[i]&lo[j];int delta=(1<<j)-(1<<i);
    return (x&~(a|b))|((x&a)>>delta)|((x&b)<<delta);
}
struct F {U s,sat;int c;};
F describe(U s,int d){
    U one=0,two=0,three=0;
    for(int j=0;j<d;++j){U n=flip(s,j);three|=two&n;two|=one&n;one|=n;}
    if(three&s)return {s,0,0};
    int edges=(std::popcount(one&s)+std::popcount(two&s))/2;
    U rest=s;int nc=0;
    while(rest){
        U front=rest&-rest;rest^=front;++nc;
        while(front){U neighbours=0;for(int j=0;j<d;++j)neighbours|=flip(front,j);
            front=neighbours&rest;rest^=front;}
    }
    return {s,two&s,(nc==std::popcount(s)-edges)?nc:0};
}
struct Catalogue {
    std::vector<F> labelled,representatives;
    std::unordered_set<U> seen;
    void orbit(U root,int d){
        if(!seen.insert(root).second)return;
        auto f=describe(root,d);if(!f.c)std::abort();representatives.push_back(f);
        std::vector<U> q{root};
        for(std::size_t i=0;i<q.size();++i){
            U v=q[i];labelled.push_back(describe(v,d));
            for(int j=0;j<d;++j){
                U w=j?swap_axes(v,j-1,j):flip(v,0);
                if(seen.insert(w).second)q.push_back(w);
            }
        }
    }
};
bool admissible(const F&a,const F&b){return !(a.sat&b.s)&&!(a.s&b.sat);}
bool forest_pair(const F&a,const F&b,int need){
    U x=a.s,y=b.s;int c=0;
    while(x||y){
        U f=x?(x&-x):0,g=f?0:(y&-y);x^=f;y^=g;
        if(++c>need)return false;
        while(f||g){
            U nf=g,ng=f;
            for(int j=0;j<6;++j){nf|=flip(f,j);ng|=flip(g,j);}
            f=nf&x;g=ng&y;x^=f;y^=g;
        }
    }
    return c==need;
}
struct Layer {F f;U nonisolated;int residual;};
using Layers=std::vector<std::vector<Layer>>;
Layers compatible_layers(U fixed,U forbidden,int limit,const std::array<std::vector<F>,9>& four){
    Layers result(limit+1);
    std::array<std::array<std::vector<F>,9>,2> allowed;
    for(int side=0;side<2;++side){
        U a=(fixed>>(16*side))&65535,t=(forbidden>>(16*side))&65535;
        for(int i=0;i<=limit;++i)for(auto& f:four[i])
            if(!(f.s&t)&&!(f.sat&a))allowed[side][i].push_back(f);
    }
    for(int j=0;j<=limit;++j)for(int i=0;i<=j;++i)
        for(auto& x:allowed[0][i])for(auto& y:allowed[1][j-i])if(admissible(x,y)){
            U s=x.s|(y.s<<16);F f=describe(s,5);
            if(!f.c||(f.sat&fixed))continue;
            U near=0;for(int b=0;b<5;++b)near|=flip(s,b);
            result[j].push_back({f,near&s,f.c-std::popcount(s&fixed)});
        }
    return result;
}
void stream_seven(int t,const std::array<Catalogue,4>& six,const std::array<std::vector<F>,9>& four){
    int best=1000;U witness_a=0,witness_b=0;
    for(int h=0;h<=t/2;++h)for(auto& a:six[h].representatives){
        int left=t-h;U low=a.s&0xffffffffu,high=a.s>>32;
        auto L=compatible_layers(low,a.sat&0xffffffffu,left,four);
        auto R=compatible_layers(high,a.sat>>32,left,four);
        for(int k=0;k<=left;++k)for(auto& x:L[k])for(auto& y:R[left-k]){
            U cross=x.f.s&y.f.s;
            int c=a.c+x.residual+y.residual-std::popcount(cross);
            if(c<=0||c>=best||!admissible(x.f,y.f))continue;
            if(cross&((x.nonisolated&low)|(y.nonisolated&high)))continue;
            F b{x.f.s|(y.f.s<<32),0,0};
            if(forest_pair(a,b,c)){best=c;witness_a=a.s;witness_b=b.s;}
        }
    }
    std::cout<<"stream "<<64-t<<' '<<best<<' '<<witness_a<<' '<<witness_b<<std::endl;
}
struct Transform {
    std::array<std::array<U,256>,4> table{};
    U apply(U x)const{return table[0][x&255]|table[1][x>>8&255]|table[2][x>>16&255]|table[3][x>>24&255];}
};
std::vector<Transform> stabilizer(U s){
    std::array<int,5> perm{0,1,2,3,4};std::vector<Transform> group;
    do{
        std::array<int,32> dest{};
        for(int v=1;v<32;++v)dest[v]=dest[v&(v-1)]|(1<<perm[std::countr_zero(unsigned(v))]);
        for(int shift=0;shift<32;++shift){
            U image=0;for(U q=s;q;q&=q-1)image|=U(1)<<(dest[std::countr_zero(q)]^shift);
            if(image!=s)continue;
            group.emplace_back();auto& trans=group.back();
            for(int block=0;block<4;++block)for(unsigned x=1;x<256;++x)
                trans.table[block][x]=trans.table[block][x&(x-1)]|(U(1)<<(dest[block*8+std::countr_zero(x)]^shift));
        }
    }while(std::next_permutation(perm.begin(),perm.end()));
    return group;
}
void marked_six_three(Catalogue& result,const std::array<Catalogue,3>& five,const std::array<std::vector<F>,9>& four){
    // One five-face has at least fifteen vertices. Normalize it, and quotient
    // its partner only by the stabilizer. A few equivalences between different
    // choices of marked face may remain; all seven-face joins stay exhaustive.
    for(int h=0;h<=1;++h)for(auto& a:five[h].representatives){
        auto possible=compatible_layers(a.s,a.sat,3-h,four);auto group=stabilizer(a.s);
        std::unordered_set<U> marked;
        for(auto& b:possible[3-h]){
            U w=b.f.s;if(marked.count(w))continue;
            auto z=describe(a.s|(w<<32),6);if(!z.c)continue;
            for(auto& trans:group)marked.insert(trans.apply(w));
            result.representatives.push_back(z);
        }
    }
    std::cout<<"marked_six 3 "<<result.representatives.size()<<std::endl;
}
using Permutation6=std::array<unsigned char,64>;
U transform6(U s,const Permutation6& map){
    U result=0;
    for(;s;s&=s-1)result|=U(1)<<map[std::countr_zero(s)];
    return result;
}
std::vector<Permutation6> stabilizer6(U mask){
    std::array<int,6> axes{0,1,2,3,4,5};
    std::vector<Permutation6> group;
    do{
        Permutation6 perm{};
        for(unsigned v=1;v<64;++v)perm[v]=perm[v&(v-1)]|(1<<axes[std::countr_zero(v)]);
        U rotated=transform6(mask,perm);
        std::array<U,64> moved{};moved[0]=rotated;
        for(unsigned shift=0;shift<64;++shift){
            if(shift)moved[shift]=flip(moved[shift&(shift-1)],std::countr_zero(shift));
            if(moved[shift]!=mask)continue;
            auto map=perm;for(auto& dest:map)dest^=shift;
            group.push_back(map);
        }
    }while(std::next_permutation(axes.begin(),axes.end()));
    return group;
}
void marked_seven(int t,const std::array<Catalogue,4>& six){
    std::ofstream out("marked-seven-"+std::to_string(64-t)+".txt");
    std::size_t marked=0,placements=0;
    for(int h=0;h<=t/2;++h)for(const auto& a:six[h].representatives){
        auto group=stabilizer6(a.s);
        std::unordered_set<U> seen;
        for(const auto& b:six[t-h].labelled){
            if(!admissible(a,b)||seen.count(b.s))continue;
            int c=a.c+b.c-std::popcount(a.s&b.s);
            if(c<=0||!forest_pair(a,b,c))continue;
            auto before=seen.size();
            for(const auto& map:group)seen.insert(transform6(b.s,map));
            auto orbit=seen.size()-before;
            if(!orbit||group.size()%orbit)std::abort();
            auto first_orbit=46080/group.size();
            auto count=first_orbit*orbit*(2*h==t?1:2);
            out<<a.s<<' '<<b.s<<' '<<c<<' '<<count<<'\n';
            ++marked;placements+=count;
        }
    }
    std::cout<<"marked_seven "<<64-t<<' '<<marked<<' '<<placements<<std::endl;
}
void stream_marked(int t,const std::array<Catalogue,4>& six,const std::array<std::vector<F>,9>& four){
    std::ofstream out("stream-marked-seven-"+std::to_string(64-t)+".txt");
    std::size_t marked=0,placements=0;
    for(int h=0;h<=t/2;++h)for(const auto& a:six[h].representatives){
        U low=a.s&0xffffffffu,high=a.s>>32;
        auto L=compatible_layers(low,a.sat&0xffffffffu,t-h,four);
        auto R=compatible_layers(high,a.sat>>32,t-h,four);
        auto group=stabilizer6(a.s);
        std::unordered_set<U> seen;
        for(int k=0;k<=t-h;++k)for(const auto& x:L[k])for(const auto& y:R[t-h-k]){
            U cross=x.f.s&y.f.s;
            if(!admissible(x.f,y.f)||(cross&((x.nonisolated&low)|(y.nonisolated&high))))continue;
            U s=x.f.s|(y.f.s<<32);
            if(seen.count(s))continue;
            int c=a.c+x.residual+y.residual-std::popcount(cross);
            if(c<=0||!forest_pair(a,F{s,0,0},c))continue;
            auto before=seen.size();
            for(const auto& map:group)seen.insert(transform6(s,map));
            auto orbit=seen.size()-before;
            if(!orbit||group.size()%orbit)std::abort();
            auto count=(46080/group.size())*orbit*(2*h==t?1:2);
            out<<a.s<<' '<<s<<' '<<c<<' '<<count<<'\n';
            ++marked;placements+=count;
        }
    }
    std::cout<<"stream_marked_seven "<<64-t<<' '<<marked<<' '<<placements<<std::endl;
}
int main(int argc,char**argv){
    int deficit=argc>1?std::stoi(argv[1]):1;
    if(deficit<0||deficit>2)return 2;
    for(int i=0;i<6;++i)for(int v=0;v<64;++v)if(!(v&(1<<i)))lo[i]|=U(1)<<v;
    std::array<Catalogue,3> five;
    std::array<Catalogue,4> six;
    std::array<std::vector<F>,9> four;
    for(U mask=1;mask<65536;++mask){
        int t=8-std::popcount(mask);if(t<0)continue;
        F f=describe(mask,4);if(f.c)four[t].push_back(f);
    }
    // Generate the entire labelled five-face input from literal four-face pairs.
    for(int t=0;t<=deficit;++t){
        std::size_t total=0;
        for(int k=0;k<=t;++k)for(auto& a:four[k])for(auto& b:four[t-k]){
            if(!admissible(a,b))continue;U z=a.s|(b.s<<16);
            if(!describe(z,5).c)continue;
            if(!five[t].seen.count(z))five[t].orbit(z,5);
            ++total;
        }
        if(total!=five[t].labelled.size())return 4;
        std::cout<<"five "<<16-t<<' '<<total<<std::endl;
    }
    for(int t=0;t<=deficit;++t){
        for(int h=0;h<=t/2;++h)for(auto&a:five[h].representatives)
            for(auto&b:five[t-h].labelled)if(admissible(a,b)){
                U z=a.s|(b.s<<32);
                if(!six[t].seen.count(z)&&describe(z,6).c)six[t].orbit(z,6);
            }
        std::cout<<"six "<<t<<' '<<six[t].representatives.size()<<' '<<six[t].labelled.size()<<std::endl;
    }
    for(int t=0;t<=deficit;++t){
        int best=1000;U witness_a=0,witness_b=0;
        for(int h=0;h<=t/2;++h)for(auto&a:six[h].representatives)
            for(auto&b:six[t-h].labelled)if(admissible(a,b)){
                int c=a.c+b.c-std::popcount(a.s&b.s);
                if(c>0&&c<best&&forest_pair(a,b,c)){best=c;witness_a=a.s;witness_b=b.s;}
            }
        std::cout<<"seven "<<64-t<<' '<<best<<' '<<witness_a<<' '<<witness_b<<std::endl;
    }
    if(argc>2 && std::string(argv[2])=="marked"){
        for(int t=0;t<=deficit;++t)marked_seven(t,six);
    }else if(argc>3 && std::string(argv[2])=="streammarked"){
        int last=std::stoi(argv[3]);if(last<0||last>2*deficit+1)return 2;
        for(auto& cat:six){cat.seen.clear();cat.labelled.clear();cat.labelled.shrink_to_fit();}
        for(int t=0;t<=last;++t)stream_marked(t,six,four);
    }else if(argc>2){
        int last=std::stoi(argv[2]);if(last>7||(last>2*deficit+1&&deficit!=2))return 2;
        for(auto& cat:six){cat.seen.clear();cat.labelled.clear();cat.labelled.shrink_to_fit();}
        if(last>=6)marked_six_three(six[3],five,four);
        for(int t=0;t<=last;++t)stream_seven(t,six,four);
    }
}
