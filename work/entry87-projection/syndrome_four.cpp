// All weight-four changes of the neighbour parity checks against one reference.
// Necessary component/endpoint defects of a triple can be repaired only if
// the fourth check is within distance three of an offending anchor.
#define PARITY_CUBE_ONLY
#include "two_parity.cpp"
#undef main
using Mask=array<uint64_t,4>;
struct Filter {
    Cube c;
    array<bool,512> bad{},leaf{};int nbad=0,nleaf=0;
    array<vector<int>,512> local;
    vector<int> marked;
    explicit Filter():c(1){}
    void refresh(int v){
        bool b=c.selected[v] && (c.degree[v]==0 || (c.degree[v]==1 && c.tips[v]==0));
        bool l=c.selected[v] && c.degree[v]==1;
        nbad+=int(b)-bad[v];nleaf+=int(l)-leaf[v];bad[v]=b;leaf[v]=l;
    }
    void flip(int w){
        for(int b=0;b<9;++b)c.toggle(w^(1<<b));
        for(int v:local[w])refresh(v);
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int p=stoi(argv[1]),start=stoi(argv[2]),stop=stoi(argv[3]);
    if(start<0 || start>=stop || stop>256)return 2;
    vector<int> checks,anchors;
    for(int v=0;v<512;++v)(popcount(unsigned(v))%2==p?anchors:checks).push_back(v);
    Filter f;
    array<Mask,512> near{};
    for(int i=0;i<256;++i){
        int w=checks[i];
        for(int v:anchors)if(popcount(unsigned(v^w))<=3){
            f.local[w].push_back(v);near[v][i/64]|=uint64_t(1)<<(i%64);
        }
    }
    int x;while(cin>>x){
        if(x<0 || x>=512 || popcount(unsigned(x))%2!=p || f.c.selected[x])return 2;
        f.c.toggle(x);
    }
    if(f.c.n!=96)return 2;
    for(int v:anchors)f.refresh(v);
    uint64_t triples=0,tuples=0,near_pass=0,size_pass=0,degree_pass=0,conn_pass=0;
    for(int i=start;i<stop;++i){f.flip(checks[i]);
        for(int j=i+1;j<256;++j){f.flip(checks[j]);
            for(int k=j+1;k<255;++k){
                f.flip(checks[k]);++triples;tuples+=255-k;
                Mask allowed{};for(int h=0;h<4;++h)allowed[h]=~uint64_t(0);
                if(f.nbad || f.nleaf>2){
                    vector<int> leaves;
                    for(int v:anchors){
                        if(f.bad[v])for(int h=0;h<4;++h)allowed[h]&=near[v][h];
                        if(f.leaf[v])leaves.push_back(v);
                    }
                    // With more than two leaves at most two may be untouched.
                    // Any fourth check must hit at least one from each triple.
                    if(leaves.size()>2){
                        Mask zero{},one{};for(auto &v:zero)v=~uint64_t(0);
                        Mask two{};
                        for(int v:leaves)for(int h=0;h<4;++h){
                            uint64_t in=near[v][h],out=~in;
                            two[h]=(two[h]&in)|(one[h]&out);
                            one[h]=(one[h]&in)|(zero[h]&out);
                            zero[h]&=in;
                        }
                        for(int h=0;h<4;++h)allowed[h]&=zero[h]|one[h]|two[h];
                    }
                }
                for(int h=(k+1)/64;h<4;++h){
                    uint64_t avail=allowed[h];
                    if(h==(k+1)/64)avail&=~uint64_t(0)<<((k+1)%64);
                    near_pass+=popcount(avail);
                    while(avail){
                        int t=64*h+countr_zero(avail);avail&=avail-1;
                        int w=checks[t];
                        if(f.c.n+9-2*f.c.count[w]!=96)continue;
                        ++size_pass;
                        for(int b=0;b<9;++b)f.c.toggle(w^(1<<b));
                        if(f.c.degrees_ok()){
                            ++degree_pass;
                            if(f.c.connected()){
                                ++conn_pass;cout<<checks[i]<<' '<<checks[j]<<' '<<checks[k]<<' '<<w<<'\n';
                            }
                        }
                        for(int b=0;b<9;++b)f.c.toggle(w^(1<<b));
                    }
                }
                f.flip(checks[k]);
            }f.flip(checks[j]);
        }f.flip(checks[i]);
    }
    cout<<"count "<<triples<<' '<<tuples<<' '<<near_pass<<' '<<size_pass<<' '<<degree_pass<<' '<<conn_pass<<'\n';
}
