// Fuse two nonadjacent Q7 layers. Opposite-colour choices are possible
// precisely at unoccupied, exclusive joining endpoints of the two anchors.
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <utility>
#include <vector>
using namespace std;
struct Mask{uint64_t a,b;};
Mask operator|(Mask x,Mask y){return {x.a|y.a,x.b|y.b};}
Mask operator&(Mask x,Mask y){return {x.a&y.a,x.b&y.b};}
Mask minusset(Mask x,Mask y){return {x.a&~y.a,x.b&~y.b};}
Mask one(int v){return v<64?Mask{1ull<<v,0}:Mask{0,1ull<<(v-64)};}
bool contains(Mask x,int v){return (x&one(v)).a || (x&one(v)).b;}
bool empty(Mask x){return !(x.a|x.b);}
int weight(Mask x){return __builtin_popcountll(x.a)+__builtin_popcountll(x.b);}
Mask hood[128];
struct Arm {vector<int> q;Mask mask{};};
vector<Arm> readarms(){
    int n;cin>>n;vector<Arm> result;
    for(int j=0;j<n;++j){
        string w;cin>>w;Arm z;int v=0;z.q={0};z.mask=one(0);
        for(char c:w){v^=1<<(c-'0');z.q.push_back(v);z.mask=z.mask|one(v);}
        result.push_back(z);
    }
    return result;
}
struct Trial{
    int a,c,b,d,dist;
    int upper;
};
int main(int argc,char**argv){
    if(argc!=3 && argc!=4)return 2;
    int requested=stoi(argv[1]);int scan=stoi(argv[2]);
    for(int v=0;v<128;++v){hood[v]=one(v);for(int j=0;j<7;++j)hood[v]=hood[v]|one(v^(1<<j));}
    auto left=readarms();auto rights=readarms();uint64_t oriented=0,tested=0,safe=0;
    // For every pair, try chosen symmetries and translations. Count the best
    // optimistic size from parity in the shared free address set. The two
    // unfixed layers are opposite in Q2; they may reuse every free address.
    uint64_t state=0x9e3779b97f4a7c15ull;
    auto next=[&](){state^=state<<13;state^=state>>7;state^=state<<17;return state;};
    Mask ev{};for(int v=0;v<128;++v)if(!__builtin_parity(v))ev=ev|one(v);
    for(int round=0;round<scan;++round){
        int li=next()%left.size(),ri=next()%rights.size();auto &L=left[li],&R=rights[ri];
        array<int,7> perm{0,1,2,3,4,5,6};for(int j=6;j>0;--j)swap(perm[j],perm[next()%(j+1)]);
        int shift=next()%128;
        if(argc==4 && string(argv[3])=="correlated"){
            for(int j=0;j<7;++j)perm[j]=j;
            if(next()&1){int i=next()%7,j=next()%7;swap(perm[i],perm[j]);}
            int u=R.q[next()%R.q.size()];int image=0;
            for(int j=0;j<7;++j)if(u>>j&1)image^=1<<perm[j];
            shift=image^L.q[next()%L.q.size()];
        }
        Mask cm{};int c0=shift,c1=0;vector<int> raw;
        for(int v:R.q){int z=shift;for(int j=0;j<7;++j)if(v>>j&1)z^=1<<perm[j];cm=cm|one(z);raw.push_back(z);c1=z;}
        ++oriented;
        // L is the first layer. Its last site is the first vertical join.
        // R is the third layer. Its two endpoints must be exclusive of L,
        // and the first join must be exclusive of R. Otherwise the last
        // layer's root or the middle bridge necessarily makes an extra edge.
        int a=L.q.back();
        if(contains(cm,a)||contains(L.mask,c0)||contains(L.mask,c1))continue;
        ++safe;
        Mask free=minusset(Mask{~0ull,~0ull},L.mask|cm);
        auto component=[&](Mask allowed,int root){
            Mask seen=one(root),fr=seen;
            while(!empty(fr)){
                Mask nxt{};uint64_t low=fr.a,high=fr.b;
                while(low){int b=__builtin_ctzll(low);low&=low-1;nxt=nxt|hood[b];}
                while(high){int b=__builtin_ctzll(high);high&=high-1;nxt=nxt|hood[64+b];}
                fr=minusset(nxt&allowed,seen);seen=seen|fr;
            }return seen;
        };
        auto capacity=[&](Mask domain,int root,int other,bool two){
            Mask comp=component(domain,root);
            if(two && !contains(comp,other))return 0;
            int e=weight(comp&ev),o=weight(comp)-e;
            if(!__builtin_parity(root))swap(e,o); // o counts the root colour
            if(two){
                if(__builtin_parity(root^other))return 2*min(e,o);
                return 2*min(e,o-1)+1;
            }
            return min(2*o,2*e+1);
        };
        for(int v=0;v<2;++v){
            int b=v?c1:c0,d=v?c0:c1;
            int capB=capacity(free|one(a)|one(b),a,b,true);
            int capD=capacity(free|one(d),d,0,false);
            if(!capB||!capD)continue;
            int upper=int(L.q.size()+R.q.size())+capB+capD;
            if(upper<requested)continue;
            ++tested;
            // Recover both complete anchored vertex sets. A downstream exact
            // longest-path search evaluates B and D in independent domains.
            cout<<upper<<" "<<a<<" "<<b<<" "<<d<<" "<<L.q.size();
            for(int x:L.q)cout<<" "<<x;
            cout<<" "<<raw.size();for(int x:raw)cout<<" "<<x;
            cout<<"\n";
        }
    }
    cerr<<oriented<<" "<<safe<<" "<<tested<<"\n";
}
