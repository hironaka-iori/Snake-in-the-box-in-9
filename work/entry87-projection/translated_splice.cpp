// Keep a prefix and a translated suffix. Exhaust every induced bridge
// between them with one more edge than the deleted section.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
using Mask=bitset<512>;
array<Mask,512> closed;
struct Count {uint64_t tested=0,separated=0,reachable=0,nodes=0;};

bool bridge(int v,int end,int remaining,const Mask& blocked,
            vector<int>& chain,uint64_t& nodes){
    ++nodes;
    if(remaining==1)return popcount(unsigned(v^end))==1;
    Mask later=blocked|closed[v];
    for(int b=0;b<9;++b){
        int w=v^(1<<b);
        if(blocked[w] || w==end)continue;
        int dist=popcount(unsigned(w^end));
        if(dist>remaining-1 || (dist==1 && remaining>2))continue;
        chain.push_back(w);
        if(bridge(w,end,remaining-1,later,chain,nodes))return true;
        chain.pop_back();
    }
    return false;
}

int main(int argc,char**argv){
    if(argc!=4)return 2;
    int low=stoi(argv[1]),high=stoi(argv[2]),weight=stoi(argv[3]);
    if(low<0 || low>high || high>190 || weight<1 || weight>9 || weight%2==0)return 2;
    for(int v=0;v<512;++v){
        closed[v][v]=true;
        for(int b=0;b<9;++b)closed[v][v^(1<<b)]=true;
    }
    int n,x;cin>>n;
    if(n<=high+1 || n>512)return 2;
    vector<int> p(n);
    for(int& v:p)if(!(cin>>v) || v<0 || v>511)return 2;
    vector<Mask> prefix(n+1),suffix(n+1),right_closed(n+1);
    for(int i=0;i<n;++i)prefix[i+1]=prefix[i]|closed[p[i]];
    vector<Count> stat(high+1);
    for(int delta=1;delta<512;++delta){
        int w=popcount(unsigned(delta));
        if(w%2==0 || w>weight)continue;
        for(int i=n-1;i>=0;--i){
            x=p[i]^delta;
            suffix[i]=suffix[i+1];suffix[i].set(x);
            right_closed[i]=right_closed[i+1]|closed[x];
        }
        for(int k=low;k<=high;++k){
            Count& c=stat[k];
            for(int i=0,j=i+k+1;j<n;++i,++j){
                ++c.tested;
                if((prefix[i+1]&suffix[j]).any())continue;
                ++c.separated;
                int start=p[i],end=p[j]^delta;
                if(popcount(unsigned(start^end))>k+2)continue;
                ++c.reachable;
                Mask blocked=prefix[i]|right_closed[j+1];
                blocked[start]=true;blocked[end]=true;
                vector<int> chain;
                if(bridge(start,end,k+2,blocked,chain,c.nodes)){
                    cout<<"witness "<<k<<' '<<i<<' '<<delta;
                    for(int h=0;h<=i;++h)cout<<' '<<p[h];
                    for(int v:chain)cout<<' '<<v;
                    for(int h=j;h<n;++h)cout<<' '<<(p[h]^delta);
                    cout<<'\n';return 0;
                }
            }
        }
    }
    for(int k=low;k<=high;++k){
        const auto& c=stat[k];
        cout<<k<<' '<<c.tested<<' '<<c.separated<<' '<<c.reachable<<' '<<c.nodes<<'\n';
    }
}
