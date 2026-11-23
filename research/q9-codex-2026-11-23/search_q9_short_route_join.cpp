// Enumerate local routes through spaced anchors and solve their joint compatibility.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <iostream>
#include <random>
#include <set>
#include <fstream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
using Bits=array<uint64_t,8>;
int distanceQ(int x,int y){return popcount(unsigned(x^y));}
bool valid(const Path&p){
    for(int j=0;j<int(p.size());j++){
        if(p[j]<0||p[j]>=512)return false;
        for(int i=0;i<j;i++)if(p[i]==p[j] || ((distanceQ(p[i],p[j])==1)!=(i+1==j)))return false;
    }return true;
}
struct Route{Path path;Bits set{},boundary{};};
bool contact(const Bits&a,const Bits&b){for(int k=0;k<8;k++)if(a[k]&b[k])return true;return false;}
void insert(Bits& a,int v){a[v/64]|=1ULL<<(v%64);}
struct Join{
    Path anchors,witness;vector<vector<Route>> pool;vector<int> selected;
    array<int,512> used{},touch{};
    size_t budget,perPool;
    uint64_t nodes=0;bool limited=false,impossible=false;
    void mark(int v,int q){used[v]+=q;for(int k=0;k<9;k++)touch[v^(1<<k)]+=q;}
    void record(const Path& path,vector<Route>&out){
        Route r;r.path=path;
        for(int v:path){insert(r.set,v);insert(r.boundary,v);for(int d=0;d<9;d++)insert(r.boundary,v^(1<<d));}
        out.push_back(std::move(r));
    }
    void fill(int tip,int target,int remaining,Path&inside,vector<Route>&out){
        if(limited)return;
        if(target>=0){
            int h=distanceQ(tip,target);
            if(h>remaining||((remaining-h)&1))return;
            if(remaining==1){if(h==1)record(inside,out);return;}
        }else if(remaining==0){record(inside,out);return;}
        for(int k=0;k<9;k++){
            int v=tip^(1<<k);if(used[v])continue;
            bool finalContact=target>=0&&distanceQ(v,target)==1;
            if(target>=0 && finalContact!=(remaining==2))continue;
            if(touch[v]!=(1+int(finalContact)))continue;
            inside.push_back(v);mark(v,1);fill(v,target,remaining-1,inside,out);mark(v,-1);inside.pop_back();
            if(out.size()>perPool){limited=true;return;}
        }
    }
    void group(int start,int target,int length){
        pool.emplace_back();Path inside;fill(start,target,length,inside,pool.back());
        if(pool.back().empty()&&!limited)impossible=true;
    }
    bool dfs(vector<vector<int>> dom, int depth){
        if(++nodes>budget){limited=true;return false;}
        if(depth==pool.size()){
            witness=pool[0][selected[0]].path;reverse(witness.begin(),witness.end());
            for(int i=0;i<anchors.size();i++){
                witness.push_back(anchors[i]);auto& r=pool[i+1][selected[i+1]].path;witness.insert(witness.end(),r.begin(),r.end());
            }
            assert(valid(witness));return true;
        }
        int best=-1;
        for(int i=0;i<dom.size();i++)if(selected[i]<0&&(best<0||dom[i].size()<dom[best].size()))best=i;
        for(int candidate:dom[best]){
            auto& r=pool[best][candidate];auto child=dom;bool ok=true;
            for(int i=0;i<dom.size()&&ok;i++)if(i!=best&&selected[i]<0){
                auto& options=child[i];options.erase(remove_if(options.begin(),options.end(),[&](int c){return contact(r.boundary,pool[i][c].set);}),options.end());
                ok=!options.empty();
            }
            if(!ok)continue;selected[best]=candidate;
            if(dfs(std::move(child),depth+1))return true;
            selected[best]=-1;if(limited)return false;
        }
        return false;
    }
    bool run(Path a,const Path& lengths,int l,int r,int cap,int maxPool){
        budget=cap;perPool=maxPool;anchors=std::move(a);
        for(int i=0;i<anchors.size();i++){
            // No adjacent anchors in this model; all interior links have length at least two.
            if(used[anchors[i]]||touch[anchors[i]])return false;mark(anchors[i],1);
        }
        pool.emplace_back(); // left tip, filled after the connecting groups are built
        for(int i=0;i<lengths.size();i++){
            group(anchors[i],anchors[i+1],lengths[i]);if(impossible||limited)return false;
        }
        // Sole feasible routes constrain both growing ends. Use those routes while
        // generating tips, then leave the joint solver to check all pairs as usual.
        Bits blocked{};for(auto& opts:pool)if(opts.size()==1){
            auto& route=opts[0];if(contact(blocked,route.set))return false;
            for(int k=0;k<8;k++)blocked[k]|=route.boundary[k];
            for(int v:route.path)mark(v,1);
        }
        Path inside;fill(anchors[0],-1,l,inside,pool[0]);if(pool[0].empty()||limited)return false;
        group(anchors.back(),-1,r);if(impossible||limited)return false;
        selected.assign(pool.size(),-1);vector<vector<int>> dom(pool.size());
        for(int i=0;i<pool.size();i++){dom[i].resize(pool[i].size());iota(dom[i].begin(),dom[i].end(),0);}
        return dfs(std::move(dom),0);
    }
};
int main(int argc,char** argv){
    if(argc!=7 && argc!=9)return 2;
    bool harvest=argc==9;set<string> known;
    auto shape=[](string s){auto norm=[](string w){int next=0;array<int,9> id;id.fill(-1);for(char&c:w){int d=c-'0';if(id[d]<0)id[d]=next++;c=char('0'+id[d]);}return w;};auto f=norm(s);reverse(s.begin(),s.end());return min(f,norm(s));};
    if(harvest){ifstream catalog(argv[7]);if(!catalog)return 2;string w;while(catalog>>w)known.insert(shape(w));}
    int trials=stoi(argv[1]),seed=stoi(argv[2]),target=stoi(argv[3]),mode=stoi(argv[4]),cap=stoi(argv[5]),maxPool=stoi(argv[6]);
    vector<Path> bank;string line;
    while(getline(cin,line)){
        Path p;if(mode){istringstream in(line);int v;while(in>>v)p.push_back(v);}else{p.push_back(0);for(char c:line)p.push_back(p.back()^(1<<(c-'0')));}
        if(!mode)assert(valid(p));bank.push_back(std::move(p));
    }
    mt19937 rng(seed);int excluded=0,cutoffs=0;uint64_t nodes=0;
    for(int it=0;it<trials;it++){
        int id=rng()%bank.size();auto&p=bank[id];int n=p.size(),a=rng()%5,b=rng()%5,end=n-1-b;
        Path indices{a};
        while(end-indices.back()>=8){int adv=3+rng()%4;indices.push_back(indices.back()+adv);}
        indices.push_back(end);
        Path anchors,lens;
        for(int i:indices)anchors.push_back(p[i]);
        for(int j=1;j<indices.size();j++)lens.push_back(indices[j]-indices[j-1]);
        int extra=target-(end-a);
        for(int attempt=0;attempt<3;attempt++){
            int k=rng()%lens.size(),delta=(rng()%2==0)?-2:2;
            if(extra-delta<0||extra-delta>12||lens[k]+delta<2||lens[k]+delta>8||
               distanceQ(anchors[k],anchors[k+1])>lens[k]+delta)continue;
            if(rng()%2){lens[k]+=delta;extra-=delta;}
        }
        if(extra<0){it--;continue;}
        int left=rng()%(extra+1);Join s;
        if(s.run(anchors,lens,left,extra-left,cap,maxPool)){
            assert(s.witness.size()==target+1);
            if(harvest){
                string word;for(int j=1;j<s.witness.size();j++)word+=char('0'+countr_zero(unsigned(s.witness[j-1]^s.witness[j])));
                word=shape(word);if(known.insert(word).second){ofstream output(argv[8],ios::app);if(!output)return 3;output<<word<<endl;cout<<"SEED "<<it<<" "<<id<<" "<<word<<endl;}
                continue;
            }
            cout<<"FOUND "<<id<<" "<<it;for(int v:s.witness)cout<<" "<<v;cout<<endl;return 0;
        }
        nodes+=s.nodes;if(s.limited)cutoffs++;else excluded++;
        if((it+1)%5000==0)cout<<"AT "<<it+1<<" "<<excluded<<" "<<cutoffs<<" "<<nodes<<endl;
    }
    cout<<"DONE "<<trials<<" "<<excluded<<" "<<cutoffs<<" "<<nodes<<endl;return 0;
}

