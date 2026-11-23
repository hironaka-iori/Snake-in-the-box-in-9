// Tree edges label the eight source directions. Vertex potentials are the binary
// incidence vectors of root-to-vertex paths in those eight edge labels.
#define Q9_PARITY_LIBRARY
#include "../search_q9_fixed_parity.cpp"
#include <cassert>
#include <fstream>
#include <set>
using Bits=array<uint64_t,4>;
using Path=vector<int>;
struct Tree{array<uint8_t,9> off{};array<unsigned short,8> masks{};};
using Edges=array<pair<int,int>,8>;
vector<Tree> trees;
void grow(Edges e,int n){
    if(n==9){
        Tree t;array<bool,9> known{};known[0]=true;
        for(int i=0;i<8;i++){
            for(int j=0;j<8;j++){auto [a,b]=e[j];if(known[a]==known[b])continue;
                if(!known[a])swap(a,b);t.off[b]=t.off[a]^(1<<j);known[b]=true;}
        }
        for(int j=0;j<8;j++){auto [a,b]=e[j];t.masks[j]=(1<<a)|(1<<b);
            assert((t.off[a]^t.off[b])==(1<<j));}
        trees.push_back(t);return;
    }
    for(int v=0;v<n;v++){
        Path incident;for(int i=0;i<n-1;i++)if(e[i].first==v||e[i].second==v)incident.push_back(i);
        for(int k=0;k<(1<<(incident.size()-1));k++){
            Edges child=e;child[n-1]={v,n};
            for(int j=1;j<int(incident.size());j++)if(k>>(j-1)&1){
                auto& [a,b]=child[incident[j]];if(a==v)a=n;else b=n;
            }
            grow(child,n+1);
        }
    }
}
int image(int v,const Tree& t){
    int x=0;for(;v;v&=v-1)x^=t.masks[countr_zero(unsigned(v))];return x;
}
struct Donor{
    Path p;array<Bits,256> translates{};array<uint8_t,256> in{};
    explicit Donor(const Path& cells):p(cells){
        for(int v:p){assert(0<=v&&v<256&&!in[v]);in[v]=1;
            for(int s=0;s<256;s++){int y=v^s;translates[s][y>>6]|=uint64_t(1)<<(y&63);}}
    }
    int pairs(const Tree& t)const{
        Bits one=translates[t.off[0]],two{},three{};
        for(int i=1;i<9;i++){const Bits& m=translates[t.off[i]];
            for(int k=0;k<4;k++){three[k]|=two[k]&m[k];two[k]|=one[k]&m[k];one[k]|=m[k];}}
        int cap=0;for(int k=0;k<4;k++)cap+=popcount(two[k]&~three[k]);return cap;
    }
    // Count even anchors with no possible adjacent anchor, and with only one port.
    int obstruction(const Tree& t)const{
        array<uint8_t,256> loads{};for(int v:p)for(int s:t.off)++loads[v^s];
        int zero=0,one=0;for(int v:p){int ports=0;
            for(int s:t.off)ports+=loads[v^s]==2;zero+=ports==0;one+=ports==1;}
        return 2*zero+max(0,one-2);
    }
};
#ifndef Q9_TREE_LIBRARY
int main(int argc,char** argv){
    if(argc!=5)return 2;int start=stoi(argv[1]),finish=stoi(argv[2]),lo=stoi(argv[3]),hi=stoi(argv[4]);
    Edges base{};base[0]={0,1};base[1]={1,2};grow(base,3);assert(trees.size()==531441);
    string w;int row=-1;
    while(cin>>w){row++;if(row<start||row>=finish)continue;
        Path p{0};for(char d:w){assert(d>='0'&&d<='7');p.push_back(p.back()^(1<<(d-'0')));}
        for(int i=0;i<int(p.size());i++)for(int j=0;j<i;j++)assert(p[i]!=p[j]&&((popcount(unsigned(p[i]^p[j]))==1)==(i==j+1)));
        Donor u(p);int best=-1,bi=-1,least=999,li=-1,any=0,deep=0,unk=0;
        for(int a=lo;a<hi;a++){auto& t=trees[a];int pairs=u.pairs(t);
            if(pairs>best){best=pairs;bi=a;}
            if(pairs>=int(p.size())-1){
                any++;int b=u.obstruction(t);
                if(b<least){least=b;li=a;}
                if(b)continue;deep++;
                Path even;for(int v:p)even.push_back(image(v,t));
                Search s(even,1000000,even.size()>=97);if(s.test()){cout<<"SOURCE "<<row<<" "<<a<<endl;return 0;}unk+=s.unknown;
            }
        }
        cout<<"ROW "<<row<<" "<<p.size()<<" "<<hi-lo<<" "<<best<<" "<<bi<<" "<<any<<" "<<least<<" "<<li<<" "<<deep<<" "<<unk<<endl;
    }
}

#endif
