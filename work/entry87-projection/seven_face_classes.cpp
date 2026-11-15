// Canonical forms of marked seven-cube forests under vertex translations and axis permutations.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <vector>
using U=std::uint64_t;
using Mask=std::array<U,2>;
using Axes=std::array<int,7>;
struct Perm {Axes axes;std::array<unsigned char,128> image;};
struct Count {U weight=0;int stabilizer=0,components=0;};
int main(int argc,char**argv){
    if(argc!=3)return 2;
    std::ifstream in(argv[1]);std::ofstream out(argv[2]);
    if(!in||!out)return 3;
    std::vector<Perm> perms;Axes axes{0,1,2,3,4,5,6};
    do{
        Perm p{axes,{}};
        for(int j=0;j<7;++j)p.image[1<<axes[j]]=1<<j;
        for(unsigned v=1;v<128;++v)p.image[v]=p.image[v&(v-1)]|p.image[v&-v];
        perms.push_back(p);
    }while(std::next_permutation(axes.begin(),axes.end()));
    std::map<Mask,Count> classes;
    U low,high,weight,total=0;int c,marked=0;
    while(in>>low>>high>>c>>weight){
        Mask input{low,high},best{~U(0),~U(0)};std::vector<int> vertices;Axes ones{};
        for(int v=0;v<128;++v)if(input[v/64]>>(v%64)&1){
            vertices.push_back(v);for(int i=0;i<7;++i)ones[i]+=v>>i&1;
        }
        int n=int(vertices.size()),shift=0,free=0,stab=0;
        for(int i=0;i<7;++i){
            if(2*ones[i]>n)shift|=1<<i;
            if(2*ones[i]==n)free|=1<<i;
        }
        for(int signs=free;;signs=(signs-1)&free){
            std::array<std::array<int,7>,7> both{};Axes oriented{};
            int translation=shift|signs;
            for(int v:vertices){
                int x=v^translation;
                for(unsigned a=x;a;a&=a-1){
                    int i=std::countr_zero(a);++oriented[i];
                    for(unsigned b=x;b;b&=b-1)++both[i][std::countr_zero(b)];
                }
            }
            std::array<Axes,7> signatures{};
            for(int i=0;i<7;++i){
                auto& s=signatures[i];s[0]=oriented[i];int k=1;
                for(int j=0;j<7;++j)if(i!=j)s[k++]=129*oriented[j]+both[i][j];
                std::sort(s.begin()+1,s.end());
            }
            Axes order{0,1,2,3,4,5,6};
            std::sort(order.begin(),order.end(),[&](int i,int j){return signatures[i]<signatures[j];});
            for(const auto& p:perms){
                bool sorted=true;
                for(int j=0;j<7;++j)if(signatures[p.axes[j]]!=signatures[order[j]]){sorted=false;break;}
                if(!sorted)continue;
                Mask image{};int offset=p.image[translation];
                for(int v:vertices){int w=p.image[v]^offset;image[w/64]|=U(1)<<(w%64);}
                if(image<best){best=image;stab=1;}
                else if(image==best)++stab;
            }
            if(signs==0)break;
        }
        auto& r=classes[best];
        if(r.weight && (r.stabilizer!=stab||r.components!=c))return 4;
        r.weight+=weight;r.stabilizer=stab;r.components=c;total+=weight;++marked;
    }
    for(const auto& [mask,r]:classes){
        if(r.weight*r.stabilizer!=645120)return 5;
        out<<mask[0]<<' '<<mask[1]<<' '<<r.components<<' '<<r.weight<<' '<<r.stabilizer<<'\n';
    }
    std::cout<<marked<<' '<<classes.size()<<' '<<total<<std::endl;
}
