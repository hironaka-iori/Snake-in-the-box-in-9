#define Q8_HOST_LIBRARY
#include "search_q8_multicross_bank.cpp"

#include <sstream>
#include "q8_host_path_collection.hpp"
#include <cassert>
struct Member{
    int id,threshold;
    Path p;
    Mask mask{};
    array<Mask,256> shifts{};
    Member(int row,Path path):id(row),p(std::move(path)){
        if(!valid(p,8))abort();
        for(int x:p){mask[x/64]|=uint64_t(1)<<(x%64);for(int t=0;t<256;t++){int v=x^t;shifts[t][v/64]|=uint64_t(1)<<(v%64);}}
    }
};
int intersection(const Mask& a,const Mask& b){
    return popcount(a[0]&b[0])+popcount(a[1]&b[1])+popcount(a[2]&b[2])+popcount(a[3]&b[3]);
}
int main(int argc,char**argv){
 if(argc!=7)return 2;int extra=0;HostCollection collector(argv[4],argv[5],argv[6]);int goal=stoi(argv[1]),start=stoi(argv[2]),stride=stoi(argv[3]);if(start<0||start>=stride||goal!=191)return 2;
 vector<vector<Member>> g;string line;set<int> ids;while(getline(cin,line)){
    istringstream ss(line);int c,id,x;if(!(ss>>c>>id)||c<0||c>g.size()||!ids.insert(id).second)return 3;
    if(c==g.size())g.emplace_back();Path p;while(ss>>x)p.push_back(x);g[c].emplace_back(id,std::move(p));
    auto& m=g[c].back();auto& root=g[c][0];int lost=root.p.size()-intersection(m.mask,root.mask);
    m.threshold=2*int(m.p.size())+lost;
 }
 uint64_t covered=0,rootScans=0,tested=0,eligible=0,nodes=0,rootPairs=0;
 for(int a=0;a<g.size();a++){
    for(int b=a;b<g.size();b++){
        auto &aa=g[a],&bb=g[b];uint64_t pairs=0;int bound=-1;
        for(int i=0;i<aa.size();i++)for(int j=(a==b?i:0);j<bb.size();j++){
            if(aa[i].p.size()+bb[j].p.size()+extra<goal+1)continue;pairs++;
            bound=max(bound,aa[i].threshold+bb[j].threshold-2*(goal+1-extra)+1);
        }
        if(!pairs)continue;if((rootPairs++%stride)!=start)continue;covered+=pairs;
        array<int,8> perm{0,1,2,3,4,5,6,7};vector<Mask> images(bb.size());
        do{
            int img[256]{};for(int v=1;v<256;v++)img[v]=img[v&(v-1)]|(1<<perm[countr_zero(unsigned(v))]);
            auto image=[&](const Path& p){Mask m{};for(int x:p){int v=img[x];m[v/64]|=uint64_t(1)<<(v%64);}return m;};
            images[0]=image(bb[0].p);bool built=false;
            for(int t=0;t<256;t++){
                int shared=intersection(aa[0].shifts[t],images[0]);if(shared>bound)continue;
                if(!built){for(int j=1;j<bb.size();j++)images[j]=image(bb[j].p);built=true;}
                for(int i=0;i<aa.size();i++)for(int j=(a==b?i:0);j<bb.size();j++){
                    int k=int(aa[i].p.size()+bb[j].p.size())-goal-1+extra;
                    if(k<0||shared>aa[i].threshold+bb[j].threshold-2*(goal+1-extra)+1)continue;
                    tested++;int actual=intersection(aa[i].shifts[t],images[j]);
                    if((!extra&&!actual)||actual>2*k+1)continue;
                    eligible++;Refill r;r.goal=goal;r.vertices=aa[i].p;
                    for(int x:bb[j].p)r.vertices.push_back(256+(img[x]^t));
                    for(int x:r.vertices)r.used[x]=true;
                    bool seen=false;if(collector.enumerate(r,k,seen))return 0;
                }
            }
        }while(next_permutation(perm.begin(),perm.end()));
        rootScans++;
    }
    cout<<"AT "<<a+1<<" "<<g.size()<<" "<<rootScans<<" "<<covered<<" "<<tested<<" "<<eligible<<" "<<collector.placements<<" "<<collector.windows<<" "<<collector.newPaths<<endl;
 }
 cout<<"DONE "<<goal<<" "<<rootScans<<" "<<covered<<" "<<tested<<" "<<eligible<<" "<<collector.placements<<" "<<collector.windows<<" "<<collector.newPaths<<endl;
}
