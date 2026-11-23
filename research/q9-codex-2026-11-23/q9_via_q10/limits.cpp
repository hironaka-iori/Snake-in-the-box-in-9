// Keep a chosen set of input directions fixed. Every occurrence of every other
// direction may take any Q9 step, independently of every other occurrence.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;using Path=vector<int>;
bool valid(const Path& p){
    for(int j=0;j<int(p.size());j++)for(int i=0;i<j;i++){
        int dist=popcount(unsigned(p[i]^p[j]));if(!dist||((dist==1)!=(i+1==j)))return false;}
    return true;
}
struct Run{
    vector<Path> blocks;Path origin,answer;array<unsigned short,512> shadow{};array<bool,512> used{};
    uint64_t nodes=0,budget;
    Run(const Path& w,int start,int len,int mask,uint64_t cap):budget(cap){
        int map[16]{},j=0;for(int b=0;b<16;b++)if((1<<b)&mask)map[b]=1<<j++;
        assert(j<=9);blocks.push_back({0});
        for(int i=start;i<start+len;i++){
            int v=map[w[i]];if(v)blocks.back().push_back(blocks.back().back()^v);else blocks.push_back({0});
        }
        origin.resize(blocks.size());
    }
    void place(int block,int shift,int dir){
        origin[block]=shift;
        for(int z:blocks[block]){int v=shift^z;used[v]=dir>0;shadow[v]+=dir;
            for(int b=1;b<512;b*=2)shadow[v^b]+=dir;}
    }
    int options(int k,bool left,int endpoint,array<int,9>& shifts) const{
        int n=0;const Path& p=blocks[k];int contact=left?int(p.size())-1:0;
        for(int b=1;b<512;b*=2){int near=endpoint^b;if(used[near]||shadow[near]!=1)continue;
            int offset=near^p[contact];bool legal=true;
            for(int i=0;i<int(p.size());i++)if(i!=contact && shadow[offset^p[i]]){legal=false;break;}
            if(legal)shifts[n++]=offset;
        }return n;
    }
    int dfs(int lo,int hi){
        if(++nodes>budget)return -1;
        int n=blocks.size();if(!lo&&hi+1==n){
            for(int k=0;k<n;k++)for(int x:blocks[k])answer.push_back(x^origin[k]);
            assert(valid(answer));return 1;
        }
        array<int,9> a{},b{};int na=10,nb=10;
        if(lo)na=options(lo-1,true,origin[lo],a);
        if(!na)return 0;
        if(hi+1<n)nb=options(hi+1,false,origin[hi]^blocks[hi].back(),b);
        if(!nb)return 0;
        bool left=na<nb||(na==nb&&blocks[lo-1].size()>=blocks[hi+1].size());
        auto& choices=left?a:b;int count=left?na:nb,k=left?lo-1:hi+1;
        for(int j=0;j<count;j++){place(k,choices[j],1);int r=dfs(min(lo,k),max(hi,k));if(r)return r;place(k,choices[j],-1);}
        return 0;
    }
    int solve(){
        int center=0;for(int j=1;j<int(blocks.size());j++)if(blocks[j].size()>blocks[center].size())center=j;
        place(center,0,1);return dfs(center,center);
    }
};
int main(int argc,char**argv){
    if(argc!=9)return 2;int dim=stoi(argv[1]),fixed=stoi(argv[2]),len=stoi(argv[3]),step=stoi(argv[4]);uint64_t cap=stoull(argv[5]);int mode=stoi(argv[6]);mt19937 rng(stoul(argv[7]));ifstream in(argv[8]);string line;int row=-1;
    uint64_t attempts=0,unsat=0,unknown=0,hits=0,nodes=0,validations=0;
    while(getline(in,line)){
        istringstream is(line);int d;if(!(is>>d)||d!=dim)continue;row++;
        Path seed,w;for(int x;is>>x;)seed.push_back(x);
        assert(valid(seed));for(int k=1;k<int(seed.size());k++)w.push_back(countr_zero(unsigned(seed[k]^seed[k-1])));
        for(int mask=0;mask<(1<<dim);mask++)if(popcount(unsigned(mask))==fixed){
            for(int off=0;off+len<=int(w.size());off+=step){
                Run test(w,off,len,mask,cap);int r=test.solve();nodes+=test.nodes;attempts++;
                if(mode==1){
                    vector<int> slots,word(w.begin()+off,w.begin()+off+len);int j=0;array<int,16> map{};
                    for(int b=0;b<dim;b++)if(mask>>b&1)map[b]=j++;
                    for(int t=0;t<len;t++)if(!(mask>>word[t]&1))slots.push_back(t);else word[t]=map[word[t]];
                    if(slots.size()<=4){
                        bool any=false;auto rec=[&](auto&& self,int i)->void{
                            if(any)return;if(i<int(slots.size())){for(int v=0;v<9;v++){word[slots[i]]=v;self(self,i+1);}return;}
                            Path p{0};for(int v:word)p.push_back(p.back()^(1<<v));any=valid(p);
                        };rec(rec,0);assert(r>=0&&bool(r)==any);validations++;
                    }
                }
                if(r==1){hits++;if(hits<=10||mode==0){cout<<"FOUND "<<row<<" "<<off<<" "<<mask<<" "<<len;for(int v:test.answer)cout<<" "<<v;cout<<endl;}
                    if(mode==0)return 0;
                }else if(r<0){unknown++;cout<<"LIMIT "<<row<<" "<<mask<<" "<<off<<endl;}else unsat++;
            }
        }
        cout<<"ROW "<<row<<" "<<attempts<<" "<<hits<<" "<<unsat<<" "<<unknown<<" "<<nodes<<" "<<validations<<endl;
    }
    cout<<"DONE "<<attempts<<" "<<hits<<" "<<unsat<<" "<<unknown<<" "<<nodes<<" "<<validations<<endl;
}
