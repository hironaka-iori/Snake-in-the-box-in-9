// Exchange a whole middle at two fixed crossings, then regrow both terminal arms.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using Mask=std::array<std::uint64_t,4>;
void setbit(Mask& m,int v){m[v/64]|=std::uint64_t(1)<<(v%64);}
bool get(const Mask& m,int v){return (m[v/64]>>(v%64))&1;}
struct Prefix{
    int source;std::vector<int> a,b;Mask test{},occupied{};std::array<unsigned char,256> near{};
};
std::vector<int> read_path(){int n;std::cin>>n;std::vector<int> q(n);for(int& v:q)std::cin>>v;return q;}
void print_path(const std::vector<int>& p){std::cout<<' '<<p.size();for(int v:p)std::cout<<' '<<v;}
int main(){
    int ns,nm,k,target; if(!(std::cin>>ns>>nm>>k>>target))return 2;
    std::vector<Prefix> prefixes;std::vector<std::pair<std::vector<int>,std::vector<int>>> sources;
    for(int i=0;i<ns;++i){
        auto a=read_path(),b=read_path();
        sources.emplace_back(a,b);
        for(int ta=0;ta<=k;++ta){
            int tb=k-ta;if(ta>=int(a.size())||tb>=int(b.size()))continue;
            Prefix f;f.source=i;f.a={a.begin(),a.end()-ta};f.b={b.begin(),b.end()-tb};
            for(auto p:{&f.a,&f.b})for(int v:*p){
                setbit(f.occupied,v);if(v!=0&&v!=7)setbit(f.test,v);
                for(int j=0;j<8;++j)++f.near[v^(1<<j)];
            }
            prefixes.push_back(std::move(f));
        }
    }
    for(int index=0;index<nm;++index){
        auto M=read_path();std::array<int,8> perm{};
        std::uint64_t comparisons=0,matches=0,states=0;std::vector<int> mm(M.size()),best_middle;
        int best=1000,best_source=-1,best_left=0,best_right=0;
        for(int flip=0;flip<2;++flip){
            if(flip)std::reverse(M.begin(),M.end());
            int origin=M.front(),delta=origin^M.back();std::iota(perm.begin(),perm.end(),0);
            do{
                int projected=0;for(int b=0;b<8;++b)if(delta&(1<<b))projected|=1<<perm[b];
                if(projected!=7)continue;
                Mask middle{};int v=0;mm[0]=0;setbit(middle,0);
                for(std::size_t j=1;j<M.size();++j){
                    int step=std::countr_zero(unsigned(M[j]^M[j-1]));v^=1<<perm[step];mm[j]=v;setbit(middle,v);
                }
                if(k<0){
                    for(std::size_t i=0;i<sources.size();++i){
                        const auto& [a,b]=sources[i];std::size_t x=1,y=1;
                        while(x<a.size()&&!get(middle,a[x]))++x;
                        while(y<b.size()&&!get(middle,b[y]))++y;
                        int left=a.size()-x,right=b.size()-y;
                        if(left+right<best){best=left+right;best_left=left;best_right=right;best_source=i;best_middle=mm;}
                        ++comparisons;
                    }
                    continue;
                }
                for(auto& f:prefixes){
                    ++comparisons;bool good=true;
                    for(int j=0;j<4;++j)if(middle[j]&f.test[j]){good=false;break;}
                    if(!good)continue;
                    ++matches;auto count=f.near;Mask occupied=f.occupied;auto a=f.a,b=f.b;
                    auto toggle=[&](int w,int change){
                        occupied[w/64]^=std::uint64_t(1)<<(w%64);
                        for(int axis=0;axis<8;++axis)count[w^(1<<axis)]+=change;
                    };
                    auto grow=[&](auto&& self,bool first,int length)->bool{
                        ++states;
                        if(!length)return true;
                        if(first&&self(self,false,length))return true;
                        auto& path=first?a:b;int tip=path.back();
                        for(int j=0;j<8;++j){
                            int w=tip^(1<<j);
                            if(get(occupied,w)||get(middle,w)||count[w]!=1)continue;
                            path.push_back(w);toggle(w,1);
                            if(self(self,first,length-1))return true;
                            toggle(w,-1);path.pop_back();
                        }
                        return false;
                    };
                    if(grow(grow,true,target-int(a.size()+b.size()+mm.size()))){
                        std::cout<<"found "<<index<<' '<<f.source;print_path(a);print_path(mm);print_path(b);std::cout<<std::endl;return 0;
                    }
                }
            }while(std::next_permutation(perm.begin(),perm.end()));
        }
        if(k<0){std::cout<<"rank "<<index<<' '<<comparisons<<' '<<best<<' '<<best_source<<' '<<best_left<<' '<<best_right;print_path(best_middle);std::cout<<std::endl;}
        else std::cout<<"done "<<index<<' '<<comparisons<<' '<<matches<<' '<<states<<std::endl;
    }
}
