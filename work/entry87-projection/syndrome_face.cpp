// Distinct syndrome supports (one parity, allowed inside a small face), reused
// for all bank classes. Build each perturbation once as 8 packed words.
#define PARITY_CUBE_ONLY
#include "two_parity.cpp"
using Packed=array<uint64_t,8>;
struct Change {Packed delta{};vector<int> checks;int target;};

int main(){
    int patterns,rows;
    if(!(cin>>patterns>>rows))return 2;
    array<Packed,512> hood{};
    for(int w=0;w<512;++w)for(int b=0;b<9;++b){
        int v=w^(1<<b);hood[w][v/64]|=uint64_t(1)<<(v%64);
    }
    vector<Change> changes(patterns);
    for(auto& c:changes){
        int n;cin>>n;c.target=n%2?97:96;
        c.checks.resize(n);
        for(int& v:c.checks){
            cin>>v;
            if(v<0 || v>511 || popcount(unsigned(v))%2)return 2;
            for(int b=0;b<9;++b){
                int w=v^(1<<b);
                c.delta[w/64]^=uint64_t(1)<<(w%64);
            }
        }
    }
    for(int k=0;k<rows;++k){
        int id,geo;cin>>id>>geo;
        Packed base{};
        for(int i=0;i<96;++i){
            int v;cin>>v;
            if(popcount(unsigned(v))%2!=geo)return 2;
            // Move odd reference anchors to odd anchors and even to odd via
            // translation by one. Pattern supports are always even.
            if(geo==0)v^=1;
            base[v/64]|=uint64_t(1)<<(v%64);
        }
        uint64_t right=0,passed=0;
        for(int j=0;j<patterns;++j){
            auto& c=changes[j];Packed result{};int size=0;
            for(int i=0;i<8;++i){result[i]=base[i]^c.delta[i];size+=popcount(result[i]);}
            if(size!=c.target)continue;
            ++right;
            // Build adjacency only after a cheap screen using even connectors.
            array<uint16_t,512> degree{};
            array<bool,512> tip{};
            array<uint16_t,512> only{};
            for(int w=0;w<512;++w){
                if(popcount(unsigned(w))%2)continue;
                Packed q{};int s=0,x=0,y=0;
                for(int h=0;h<8;++h){q[h]=result[h]&hood[w][h];s+=popcount(q[h]);}
                if(s>2 || s==0)continue;
                int hits=0;
                for(int h=0;h<8;++h)for(auto n=q[h];n;n&=n-1){
                    int v=64*h+countr_zero(n);
                    if(hits++==0)x=v;else y=v;
                }
                if(s==1)tip[x]=true;
                if(s==2){
                    if(degree[x]==0)only[x]=y;
                    if(degree[y]==0)only[y]=x;
                    if(only[x]!=y || degree[x]==0)++degree[x];
                    if(only[y]!=x || degree[y]==0)++degree[y];
                }
            }
            int leaves=0;bool good=true;
            for(int h=0;h<8 && good;++h)for(auto v=result[h];v;v&=v-1){
                int x=64*h+countr_zero(v);
                if(!degree[x] || (degree[x]==1 && (++leaves>2 || (c.target==96 && !tip[x])))){
                    good=false;break;
                }
            }
            if(good){++passed;cout<<"pass "<<id<<' '<<geo<<' '<<j<<'\n';}
        }
        cout<<"count "<<id<<' '<<geo<<' '<<patterns<<' '<<right<<' '<<passed<<'\n';
    }
}
