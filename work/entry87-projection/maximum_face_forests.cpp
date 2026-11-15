// Join all half-full induced linear forests across opposite faces of a hypercube.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <vector>
using Bits=std::array<std::uint64_t,4>;
struct Forest {
    Bits occupied{},saturated{};
    std::array<unsigned char,256> component{};
    int count=0;
};
bool bit(const Bits& s,int x){return (s[x/64]>>(x%64))&1;}
void put(Bits& s,int x){s[x/64]|=std::uint64_t(1)<<(x%64);}
bool describe(const Bits& mask,int d,Forest& f){
    f=Forest{};f.occupied=mask;std::array<bool,256> seen{};
    for(int x=0;x<(1<<d);++x) if(bit(mask,x)&&!seen[x]){
        std::vector<int> todo{x};seen[x]=true;int verts=0,degs=0;
        while(!todo.empty()){
            int v=todo.back();todo.pop_back();++verts;f.component[v]=f.count;int degree=0;
            for(int b=0;b<d;++b){
                int w=v^(1<<b);if(!bit(mask,w))continue;
                ++degree;if(!seen[w]){seen[w]=true;todo.push_back(w);}
            }
            if(degree>2)return false;
            if(degree==2)put(f.saturated,v);
            degs+=degree;
        }
        if(degs!=2*(verts-1))return false;
        ++f.count;
    }
    return true;
}
void report(int d,const std::vector<Forest>& sets){
    std::map<int,int> hist;for(const auto& f:sets)++hist[f.count];
    std::cout<<d<<' '<<sets.size();
    for(auto [c,n]:hist)std::cout<<' '<<c<<' '<<n;
    std::cout<<std::endl;
}
int main(int argc,char**argv){
    int stop=argc>1?std::stoi(argv[1]):8;
    if(stop<4||stop>8)return 2;
    std::vector<Forest> previous;
    for(unsigned m=0;m<(1U<<16);++m)if(std::popcount(m)==8){
        Forest f;if(describe(Bits{m,0,0,0},4,f))previous.push_back(f);
    }
    report(4,previous);
    for(int d=5;d<=stop;++d){
        int n=1<<(d-1),words=(n+63)/64;std::vector<Forest> next;
        std::uint64_t pairs=0,degree_pass=0;
        for(const auto& a:previous)for(const auto& b:previous){
            ++pairs;bool good=true;
            for(int j=0;j<words;++j)if((a.saturated[j]&b.occupied[j])||(b.saturated[j]&a.occupied[j])){good=false;break;}
            if(!good)continue;
            ++degree_pass;Bits joined=a.occupied;
            if(n<64)joined[0]|=b.occupied[0]<<n;
            else for(int j=0;j<words;++j)joined[j+words]=b.occupied[j];
            Forest f;if(describe(joined,d,f))next.push_back(f);
        }
        std::cerr<<"pairs "<<d<<' '<<pairs<<' '<<degree_pass<<std::endl;
        report(d,next);previous=std::move(next);
    }
}
