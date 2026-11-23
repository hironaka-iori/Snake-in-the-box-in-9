// Independent check: intersect possible translation vectors for the whole arm
// in parallel, after each coordinate direction is assigned.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;using B=array<uint64_t,8>;
struct N{array<int,9> child{};bool leaf=false;};
struct Placement{
    const vector<N>& tree;array<B,512> admissible{};B origins{};
    array<int,9> phys{};uint64_t visited=0,placed=0;
    Placement(const string& a,const vector<N>& t,bool fused):tree(t){
        array<bool,512> banned{},earlier{};int x=0;
        auto ban=[](auto& it,int x){it[x]=true;for(int b=1;b<512;b*=2)it[x^b]=true;};
        ban(banned,0);for(char c:a){x^=1<<(c-'A');ban(banned,x);ban(earlier,x);}
        for(int o=0;o<512;o++){
            if(fused?o==0:(!earlier[o]&&o!=0))origins[o/64]|=uint64_t(1)<<(o%64);
            for(int d=0;d<512;d++)if(!(fused?earlier:banned)[o^d])admissible[d][o/64]|=uint64_t(1)<<(o%64);
        }
    }
    void rec(int n,int disp,int used,const B& live){
        visited++;if(tree[n].leaf)for(auto x:live)placed+=popcount(x);
        for(int i=0;i<9;i++)if(tree[n].child[i]){
            int old=phys[i],bits=old?old:511^used;
            for(int rest=bits;rest;rest&=rest-1){
                int b=rest&-rest,z=disp^b;B next;uint64_t any=0;
                for(int j=0;j<8;j++){next[j]=live[j]&admissible[z][j];any|=next[j];}
                if(!any)continue;phys[i]=b;rec(tree[n].child[i],z,used|b,next);phys[i]=old;
            }
        }
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;ifstream a(argv[1]),b(argv[2]);int fused=stoi(argv[3]);vector<N> tree(1);
    string s;int arms=0;while(b>>s){int id=0;for(char c:s){int k=c-'A',n=tree[id].child[k];if(!n){n=tree.size();tree[id].child[k]=n;tree.emplace_back();}id=n;}tree[id].leaf=true;arms++;}
    while(a>>s){Placement p(s,tree,fused);p.rec(0,0,0,p.origins);cout<<"COUNT "<<arms<<" "<<p.visited<<" "<<p.placed<<endl;}
}
