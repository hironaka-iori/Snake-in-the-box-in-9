// Bidirectional induced-path search rooted at disjoint donor intervals.
// A path using at most E outsiders loses at most |host|+E-(goal+1) host points.
// Any untouched consecutive interval must appear verbatim in that path.
#pragma once
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <deque>
#include <unordered_map>
#include <vector>

struct SeedGrow {
    using Path=std::vector<int>;
    int retainedMinimum=0;
    int dim,target,extra,slack,lost=0,outer=0;
    uint64_t nodes=0;
    std::array<uint8_t,512> host{},used{},touch{},blocked{};
    std::deque<int> line;
    Path witness;
    int hostColour[2]{},outsideColour[2]{},lostColour[2]{};
    // Every original induced claw must lose a host point. Memoize the
    // minimum extra deletions still required, even ignoring occupied vertices.
    std::array<uint64_t,512> hits{};
    std::vector<std::array<int,4>> claws;
    std::unordered_map<uint64_t,int> costs;
    uint64_t unhit=0;
    void initClaws(){
        for(int x=0;x<(1<<dim);x++)if(host[x]){
            std::array<int,4> claw{x};int k=1;
            for(int d=0;d<dim;d++)if(host[x^(1<<d)]){
                if(k==4)return; // Any partial collection remains a valid bound.
                claw[k++]=x^(1<<d);
            }
            if(k==4&&claws.size()<63){
                uint64_t bit=uint64_t(1)<<claws.size();claws.push_back(claw);unhit|=bit;
                for(int y:claw)hits[y]|=bit;
            }
        }
    }
    int minDelete(uint64_t mask){
        if(!mask)return 0;
        auto old=costs.find(mask);if(old!=costs.end())return old->second;
        auto &claw=claws[std::countr_zero(mask)];int best=64;
        for(int y:claw)best=std::min(best,1+minDelete(mask & ~hits[y]));
        costs.emplace(mask,best);return best;
    }
    void cover(int x,int sign) {
        for(int b=0;b<dim;b++){
            int y=x^(1<<b);
            if(host[y]&&!used[y]){
                if(sign>0&&!blocked[y]){lost++;lostColour[std::popcount(unsigned(y))&1]++;unhit &= ~hits[y];}
                if(sign<0&&blocked[y]==1){lost--;lostColour[std::popcount(unsigned(y))&1]--;}
            }
            blocked[y]+=sign;
        }
    }
    void occupy(int x,int sign){
        used[x]+=sign;if(!host[x]){outer+=sign;outsideColour[std::popcount(unsigned(x))&1]+=sign;}
        for(int b=0;b<dim;b++)touch[x^(1<<b)]+=sign;
    }
    int options(int x,std::array<int,9>& list){
        int n=0;
        for(int b=0;b<dim;b++){
            int y=x^(1<<b);
            if(!used[y]&&touch[y]==1&&!blocked[y]&&(host[y]||outer<extra))list[n++]=y;
        }return n;
    }
    bool search(bool left,bool right){
        nodes++;
        if(lost>slack||minDelete(unhit)>slack-lost)return false;
        if(int(line.size())>=target+1&&int(line.size())-outer>=retainedMinimum){witness.assign(line.begin(),line.end());return true;}
        if(!left&&!right)return false;
#ifdef Q9_CLEAN_INTERVALS
        bool colourPossible=false;
        for(int c=0;c<2;c++){
            int hi=(target+2)/2,lo=(target+1)/2;
            int want=std::max(outsideColour[c],hi-hostColour[c]+lostColour[c])
                    +std::max(outsideColour[1-c],lo-hostColour[1-c]+lostColour[1-c]);
            if(want<=extra){colourPossible=true;break;}
        }
        if(!colourPossible)return false;
#endif
        std::array<int,9> a{},b{};
        int na=left?options(line.front(),a):10,nb=right?options(line.back(),b):10;
        bool front=na<=nb;
        int tip=front?line.front():line.back();
        auto &opts=front?a:b;int count=std::min(na,nb);
        uint64_t before=unhit;
        for(int i=0;i<count;i++){
            int y=opts[i];
            occupy(y,1);cover(tip,1);
            if(front)line.push_front(y);else line.push_back(y);
            bool success=search(left,right);
            if(front)line.pop_front();else line.pop_back();
            cover(tip,-1);occupy(y,-1);unhit=before;
            if(success)return true;
        }
        cover(tip,1);bool success=search(left&&!front,right&&front);cover(tip,-1);unhit=before;
        return success;
    }
    bool run(const Path& a,const Path& b,int dimension,int edges,int allowed,int retained=-1){
        dim=dimension;target=edges;extra=allowed;slack=int(a.size()+b.size())+extra-edges-1;
        retainedMinimum=std::max(0,retained);
        if(retained>=0)slack=std::min(slack,int(a.size()+b.size())-retained);
        if(slack<0)return false;
        for(auto arr:{&a,&b})for(int x:*arr){host[x]=1;hostColour[std::popcount(unsigned(x))&1]++;}
        initClaws();if(minDelete(unhit)>slack)return false;
        int needed=slack+1;
        int len=(a.size()+b.size())/needed;
        while(len>1&&(a.size()/len+b.size()/len)<needed)len--;
        if(len<2)return fallback();
        // An omission from an interval avoiding all claws cannot pay for
        // hitting any claw. Use fewer disjoint intervals when they stay long.
#ifdef Q9_CLEAN_INTERVALS
        int cleanNeeded=needed-minDelete(unhit);
        if(cleanNeeded<needed){
            std::vector<Path> runs;
            for(auto arr:{&a,&b}){
                Path run;
                for(int x:*arr){if(!hits[x])run.push_back(x);else if(!run.empty()){runs.push_back(run);run.clear();}}
                if(!run.empty())runs.push_back(run);
            }
            int maxLen=0;
            for(int trial=2;trial<=int(std::max(a.size(),b.size()));trial++){
                int count=0;for(auto &r:runs)count+=r.size()/trial;
                if(count<cleanNeeded)break;maxLen=trial;
            }
            if(maxLen>=std::max(2,len-2)){
                for(auto &r:runs)for(int i=0;i+maxLen<=r.size();i+=maxLen){
                    if(root(Path(r.begin()+i,r.begin()+i+maxLen)))return true;
                    if(!--cleanNeeded)return false;
                }
            }
        }
#endif
        for(auto arr:{&a,&b})for(int off=0;off+len<=arr->size()&&needed>0;off+=len){
            --needed;
            if(root(Path(arr->begin()+off,arr->begin()+off+len)))return true;
        }
        assert(needed==0);return false;
    }
    bool root(const Path& p){
        auto before=unhit;
        for(int x:p){line.push_back(x);occupy(x,1);}
        for(int j=1;j+1<p.size();j++)cover(p[j],1);
        bool found=search(true,true);
        for(int j=1;j+1<p.size();j++)cover(p[j],-1);
        for(int x:p)occupy(x,-1);line.clear();unhit=before;
        assert(!lost&&!outer);return found;
    }
    bool fallback(){
        // A target path of positive length contains at least one cube edge.
        for(int x=0;x<(1<<dim);x++)for(int b=0;b<dim;b++){
            int y=x^(1<<b);
            if(y>x&&int(!host[x])+int(!host[y])<=extra&&root({x,y}))return true;
        }return false;
    }
};
