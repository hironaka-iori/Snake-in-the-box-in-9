// Join pairs of oriented Q8 arms at their roots in opposite layers of Q9.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <set>
#include <string>
#include <vector>
using Mask = std::array<uint64_t,4>;
struct Arm { std::vector<int> vertices; Mask mask{}; bool fresh=false; };
void mark(Mask& mask, int v){ mask[v/64] |= uint64_t{1} << (v%64); }
bool disjoint(const Mask& a, const Mask& b){
    for(int i=0;i<4;i++) if(a[i]&b[i]) return false;
    return true;
}
int main(int argc,char** argv){
    std::vector<Arm> arms;
    std::string steps;
    std::ifstream extra;
    if(argc>1){extra.open(argv[1]);if(!extra)return 5;}
    std::set<std::string> seen;
    for(int source=0;source<(argc>1?2:1);source++){
      std::istream& in=source?static_cast<std::istream&>(extra):std::cin;
      while(in >> steps){
        if(!seen.insert(steps).second)continue;
        Arm a;a.fresh=source!=0;a.vertices.push_back(0);
        for(char ch: steps){
            if(ch<'0' || ch>'7') return 2;
            int v=a.vertices.back()^(1<<(ch-'0'));
            a.vertices.push_back(v); mark(a.mask,v);
        }
        for(unsigned i=0;i<a.vertices.size();i++) for(unsigned j=0;j<i;j++){
            int d=std::popcount(unsigned(a.vertices[i]^a.vertices[j]));
            if(!d || (d==1)!=(i==j+1)) return 3;
        }
        arms.push_back(a);
      }
    }
    std::sort(arms.begin(),arms.end(),[](const Arm& a,const Arm& b){return a.vertices.size()<b.vertices.size();});
    std::array<int,8> perm{0,1,2,3,4,5,6,7};
    std::array<uint64_t,198> checked{},hits{};
    do {
        std::array<int,256> map{};
        for(int v=1;v<256;v++) map[v]=map[v&(v-1)] | (1<<perm[std::countr_zero(unsigned(v))]);
        for(size_t j=0;j<arms.size();j++){
            const auto& b=arms[j]; Mask image{};
            for(size_t n=1;n<b.vertices.size();n++) mark(image,map[b.vertices[n]]);
            for(int i=int(j);i>=0;i--){
                const auto& a=arms[i];
                int length=a.vertices.size()+b.vertices.size()-1;
                if(length<190)break;
                if(argc>1 && !a.fresh && !b.fresh)continue;
                checked[length]++;
                if(!disjoint(a.mask,image)) continue;
                hits[length]++;
                if(length<192) continue;
                for(auto v=a.vertices.rbegin();v!=a.vertices.rend();v++) std::cout<<*v<<" ";
                for(int v:b.vertices) std::cout<<(256+map[v])<<" ";
                std::cout<<"\n"; return 0;
            }
        }
    } while(std::next_permutation(perm.begin(),perm.end()));
    for(int n=190;n<=197;n++) std::cout<<n<<" "<<checked[n]<<" "<<hits[n]<<"\n";
}
