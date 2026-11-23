// Simultaneously change interior corners and grow both ends of a Q9 snake.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
int dist(int a,int b){return popcount(unsigned(a^b));}
bool valid(const Path&p){
    for(int i=0;i<int(p.size());i++){
        if(p[i]<0||p[i]>=512)return false;
        for(int j=0;j<i;j++)if(p[i]==p[j]||((dist(p[i],p[j])==1)!=(j+1==i)))return false;
    }
    return true;
}
struct Forced{
    array<uint64_t,3> hi{},lo{};
    void add(int lit){auto& bits=(lit&1)?hi:lo;bits[lit/128]|=1ULL<<((lit/2)%64);}
    bool merge(const Forced&o){
        for(int k=0;k<3;k++){hi[k]|=o.hi[k];lo[k]|=o.lo[k];if(hi[k]&lo[k])return false;}
        return true;
    }
};
struct Engine{
    Path base,alt,var,left,right,bridge,witness;
    int split;
    vector<Forced> implications;
    array<Forced,512> bans{};
    array<bool,512> dead{};
    array<int,512> used{},degree{};
    uint64_t nodes=0,limit=0;
    bool cutoff=false;
    int corners=0;
    void mark(int x,int sign){used[x]+=sign;for(int d=0;d<9;d++)degree[x^(1<<d)]+=sign;}
    bool clash(int i,int x,int j,int y) const {
        return x==y||((dist(x,y)==1)!=(abs(i-j)==1 && max(i,j)!=split));
    }
    Engine(Path segment,uint64_t budget,int seam=-1,const Path& candidates={}):base(std::move(segment)),alt(base),split(seam),limit(budget){
        int n=base.size();assert(n<=192);
        if(!candidates.empty())assert(candidates.size()==base.size());
        for(int i=1;i+1<n;i++)if(i!=split && i+1!=split)alt[i]=candidates.empty()?(base[i-1]^base[i]^base[i+1]):candidates[i];
        // An alternative conflicting with an already fixed position cannot occur.
        vector<int> fixed;for(int i=0;i<n;i++)if(base[i]==alt[i])fixed.push_back(i);
        for(size_t t=0;t<fixed.size();t++){
            int j=fixed[t];
            for(int i=1;i+1<n;i++)if(i!=j&&alt[i]!=base[i]&&clash(i,alt[i],j,base[j])){
                alt[i]=base[i];fixed.push_back(i);
            }
        }
        for(int i=0;i<n;i++){if(alt[i]==base[i])mark(base[i],1);else var.push_back(i);}
        corners=var.size();const int m=2*corners;
        vector<vector<int>> edges(m);
        for(int a=0;a<corners;a++)for(int b=0;b<a;b++){
            int i=var[a],j=var[b];
            for(int s=0;s<2;s++)for(int t=0;t<2;t++)if(clash(i,s?alt[i]:base[i],j,t?alt[j]:base[j])){
                edges[2*a+s].push_back(2*b+1-t);edges[2*b+t].push_back(2*a+1-s);
            }
        }
        implications.resize(m);
        for(int lit=0;lit<m;lit++){
            vector<bool> seen(m);Path stack{lit};seen[lit]=true;
            for(size_t k=0;k<stack.size();k++){
                int v=stack[k];implications[lit].add(v);
                for(int w:edges[v])if(!seen[w]){seen[w]=true;stack.push_back(w);}
            }
        }
        for(int a=0;a<corners;a++)for(int s=0;s<2;s++){
            int i=var[a],v=s?alt[i]:base[i];
            for(int d=-1;d<9;d++){
                int x=v^(d<0?0:(1<<d));
                if(!dead[x]&&!bans[x].merge(implications[2*a+1-s]))dead[x]=true;
            }
        }
    }
    bool connect(int remaining,int l,int r,const Forced& state){
        int tip=bridge.empty()?base[split-1]:bridge.back(),target=base[split];
        int h=dist(tip,target);
        if(h>remaining || ((h^remaining)&1))return false;
        if(remaining==1)return h==1 && visit(l,r,state);
        if(limit && nodes>=limit){cutoff=true;return false;}
        nodes++;
        for(int d=0;d<9;d++){
            int v=tip^(1<<d);
            int nextDist=dist(v,target);
            if(nextDist>remaining-1 || used[v] || dead[v])continue;
            if((nextDist==1)!=(remaining==2))continue;
            if(degree[v]!=(remaining==2?2:1))continue;
            Forced next=state;if(!next.merge(bans[v]))continue;
            mark(v,1);bridge.push_back(v);
            if(connect(remaining-1,l,r,next))return true;
            bridge.pop_back();mark(v,-1);if(cutoff)return false;
        }
        return false;
    }
    bool visit(int l,int r,const Forced& state){
        if(limit && nodes>=limit){cutoff=true;return false;}
        nodes++;
        if(!l&&!r){
            Path solution=base;Forced decisions=state;
            for(int a=0;a<corners;a++){
                auto trial=decisions;
                if(trial.merge(implications[2*a]))decisions=trial;
                else {bool ok=decisions.merge(implications[2*a+1]);assert(ok);solution[var[a]]=alt[var[a]];}
            }
            if(split>=0)solution.insert(solution.begin()+split,bridge.begin(),bridge.end());
            witness=left;reverse(witness.begin(),witness.end());witness.insert(witness.end(),solution.begin(),solution.end());witness.insert(witness.end(),right.begin(),right.end());
            assert(valid(witness));return true;
        }
        bool first=l>0;auto& arm=first?left:right;
        int tip=arm.empty()?(first?base.front():base.back()):arm.back();
        for(int d=0;d<9;d++){
            int v=tip^(1<<d);
            if(used[v]||degree[v]!=1||dead[v])continue;
            auto next=state;if(!next.merge(bans[v]))continue;
            mark(v,1);arm.push_back(v);
            if(visit(l-int(first),r-int(!first),next))return true;
            arm.pop_back();mark(v,-1);if(cutoff)return false;
        }
        return false;
    }
};
#ifndef Q9_CORNER_DRIVER
int main(int argc,char**argv){
    if(argc!=7)return 2;
    int target=stoi(argv[1]),lo=stoi(argv[2]),hi=stoi(argv[3]),offset=stoi(argv[4]),stride=stoi(argv[5]);
    uint64_t budget=stoull(argv[6]);int idx=-1;string word;
    while(cin>>word){idx++;if(idx%stride!=offset)continue;
        Path p{0};for(char s:word){if(s<'0'||s>'8')return 2;p.push_back(p.back()^(1<<(s-'0')));}assert(valid(p));
        for(int trim=lo;trim<=hi;trim++){
            int tests=0,cuts=0,maxvar=0;uint64_t visited=0;
            for(int a=0;a<=trim;a++){
                Engine model(Path(p.begin()+a,p.end()-(trim-a)),budget);maxvar=max(maxvar,model.corners);
                int need=target+1-model.base.size();
                for(int l=0;l<=need;l++){
                    model.nodes=0;model.cutoff=false;tests++;
                    if(model.visit(l,need-l,Forced{})){
                        cout<<"FOUND "<<idx<<" "<<trim<<" "<<a<<" "<<l<<" "<<maxvar;
                        for(int x:model.witness)cout<<" "<<x;cout<<endl;return 0;
                    }
                    cuts+=model.cutoff;visited+=model.nodes;
                }
            }
            cout<<"ROW "<<idx<<" "<<trim<<" "<<tests<<" "<<cuts<<" "<<visited<<" "<<maxvar<<endl;
        }
    }
}
#endif

