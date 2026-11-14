// Enumerate prefix/suffix pivot orientations. For fixed translated endpoint z,
// assign its permutation by DFS until a prefix maps into a forbidden address.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <tuple>
#include <vector>
using namespace std;
using Mask=array<uint64_t,8>;
void insert(Mask& m,int x){m[x/64]|=uint64_t(1)<<(x%64);}
bool has(const Mask&m,int x){return (m[x/64]>>(x%64))&1;}
Mask join(const Mask&a,const Mask&b){Mask m{};for(int i=0;i<8;++i)m[i]=a[i]|b[i];return m;}
array<Mask,512> hood;

bool bridge(int head,int end,int remaining,Mask blocked,vector<int>& inside,uint64_t& nodes){
    ++nodes;
    if(remaining==1)return popcount(unsigned(head^end))==1;
    Mask next=join(blocked,hood[head]);
    for(int b=0;b<9;++b){
        int v=head^(1<<b);if(v==end || has(blocked,v))continue;
        int dist=popcount(unsigned(v^end));
        if(dist>remaining-1 || (dist==1 && remaining>2))continue;
        inside.push_back(v);
        if(bridge(v,end,remaining-1,next,inside,nodes))return true;
        inside.pop_back();
    }
    return false;
}
int main(int argc,char**argv){
    if(argc!=5)return 2;
    int k=stoi(argv[1]),first=stoi(argv[2]),last=stoi(argv[3]),axis_mode=stoi(argv[4]);
    vector<int> P;for(int v;cin>>v;)P.push_back(v);
    for(int v=0;v<512;++v){insert(hood[v],v);for(int b=0;b<9;++b)insert(hood[v],v^(1<<b));}
    uint64_t cells=0,orient=0,arc_nodes=0,searches=0,bridge_nodes=0;
    for(int cut=first;cut<last && cut+k+1<int(P.size());++cut){
        int end_index=cut+k+1;
        vector<int> L(P.begin(),P.begin()+cut+1),R(P.begin()+end_index,P.end());
        // Always place the longer arm first, then rotate the shorter one.
        bool reversed=R.size()>L.size();
        if(reversed){swap(L,R);reverse(L.begin(),L.end());reverse(R.begin(),R.end());}
        Mask forbidden{},nongap{};
        for(int v:L)forbidden=join(forbidden,hood[v]);
        for(int z=0;z+1<int(L.size());++z)nongap=join(nongap,hood[L[z]]);
        insert(nongap,L.back());
        vector<int> raw;array<int,9> first_of;first_of.fill(-1);int nd=0;
        for(size_t i=1;i<R.size();++i){
            int b=countr_zero(unsigned(R[i]^R[i-1]));
            if(first_of[b]<0)first_of[b]=nd++;
            raw.push_back(first_of[b]);
        }
        for(int end=0;end<512;++end){
            if(has(forbidden,end))continue;
            int dist=popcount(unsigned(end^L.back()));
            if(dist>k+2 || (dist^(k+2))&1)continue;
            ++cells;
            vector<int> placed{end};array<int,9> names{};
            auto visit=[&](auto&& self,int index,int mapped,int used)->bool{
                ++arc_nodes;
                int old_size=int(placed.size());
                while(index<int(raw.size()) && raw[index]<mapped){
                    int v=placed.back()^(1<<names[raw[index]]);
                    if(has(forbidden,v)){placed.resize(old_size);return false;}
                    placed.push_back(v);++index;
                }
                if(index==int(raw.size())){
                    ++orient;
                    Mask blocked=nongap;
                    for(size_t j=1;j<placed.size();++j)blocked=join(blocked,hood[placed[j]]);
                    insert(blocked,end);vector<int> inner;++searches;
                    if(bridge(L.back(),end,k+2,blocked,inner,bridge_nodes)){
                        cout<<"witness "<<cut<<' '<<int(reversed);
                        for(int x:L)cout<<' '<<x;
                        for(int x:inner)cout<<' '<<x;
                        for(int x:placed)cout<<' '<<x;
                        cout<<'\n';return true;
                    }
                }else{
                    for(int b=0;b<9;++b){
                        if(used&(1<<b))continue;
                        if(axis_mode==1 && b!=countr_zero(unsigned(R[index]^R[index+1])))continue;
                        names[mapped]=b;
                        if(self(self,index,mapped+1,used|(1<<b)))return true;
                    }
                }
                placed.resize(old_size);return false;
            };
            if(visit(visit,0,0,0))return 0;
        }
    }
    cout<<"count "<<cells<<' '<<orient<<' '<<arc_nodes<<' '<<searches<<' '<<bridge_nodes<<'\n';
}
