// Search increasing-index induced subpaths of each raw crossover, then freely extend both tips.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using Mask=std::bitset<512>;
std::array<Mask,512> closed;
std::vector<int> raw,path,best;
std::vector<std::vector<int>> after;
std::vector<int> upper;
long long nodes=0, cores=0;
int target=192, radius=4;

bool valid(const std::vector<int>& p){
    for(size_t i=0;i<p.size();i++) for(size_t j=0;j<i;j++){
        int d=std::popcount(unsigned(p[i]^p[j]));
        if(!d || (d==1)!=(j+1==i))return false;
    }
    return true;
}
void record(std::vector<int> p){
    if(p.size()<=best.size())return;
    if(!valid(p))std::abort();
    best=std::move(p);
    if(int(best.size())>target){
        std::cout<<"FOUND";for(int v:best)std::cout<<" "<<v;std::cout<<std::endl;
        std::exit(0);
    }
}
std::set<std::vector<int>> forms;
std::vector<int> normalize(const std::vector<int>& p){
    std::array<int,9> dims;dims.fill(-1);int n=0;
    std::vector<int> seq;
    for(size_t i=1;i<p.size();i++){
        int bit=std::countr_zero(unsigned(p[i-1]^p[i]));
        if(dims[bit]<0)dims[bit]=n++;
        seq.push_back(dims[bit]);
    }
    return seq;
}
void right(int available, Mask blocked, std::vector<int>& p){
    if(p.size()==192){
        auto f=normalize(p);
        std::vector<int> rev(p.rbegin(),p.rend());auto r=normalize(rev);
        if(forms.insert(std::min(f,r)).second){
            if(!valid(p))std::abort();
            std::cout<<"SEED";for(int v:p)std::cout<<" "<<v;std::cout<<std::endl;
        }
    }
    if(p.size()>best.size())record(p);
    if(!available)return;
    int x=p.back();
    for(int d=0;d<9;d++){
        int y=x^(1<<d);
        if(blocked[y])continue;
        p.push_back(y);right(available-1,blocked|closed[x],p);p.pop_back();
    }
}
void left(int remaining, Mask blocked, Mask tail_block, std::vector<int>& front){
    std::vector<int> p(front.rbegin(),front.rend());
    p.insert(p.end(),path.begin(),path.end());
    right(radius,tail_block,p);
    if(!remaining)return;
    int x=front.empty()?path.front():front.back();
    for(int d=0;d<9;d++){
        int y=x^(1<<d);
        if(blocked[y])continue;
        front.push_back(y);left(remaining-1,blocked|closed[x],tail_block|closed[y],front);front.pop_back();
    }
}
void walk(int i,Mask blocked){
    ++nodes;
    int x=raw[i];path.push_back(x);
    if(int(path.size())+2*radius>=target+1){
        ++cores;
        Mask head;for(size_t j=1;j<path.size();j++)head|=closed[path[j]];
        std::vector<int> front;
        left(radius,head,blocked,front);
    }
    Mask next=blocked|closed[x];
    for(int j:after[i]){
        if(int(path.size())+upper[j]+2*radius<target+1 || blocked[raw[j]])continue;
        walk(j,next);
    }
    path.pop_back();
}
int main(int argc,char**argv){
    if(argc!=3 && argc!=4)return 2;
    target=std::stoi(argv[1]);radius=std::stoi(argv[2]);
    for(int v=0;v<512;v++){
        closed[v].set(v);for(int d=0;d<9;d++)closed[v].set(v^(1<<d));
    }
    int count=0;
    for(std::string line;std::getline(std::cin,line);){
        std::istringstream in(line);raw.clear();int v;
        while(in>>v){if(v<0||v>=512)return 3;raw.push_back(v);}
        if(raw.empty())continue;
        if(argc==4){
            // Offer the opposite square corner at each collision or chord endpoint.
            std::vector<bool> conflict(raw.size());
            for(size_t i=0;i<raw.size();i++)for(size_t j=0;j+1<i;j++){
                if(std::popcount(unsigned(raw[i]^raw[j]))<=1)conflict[i]=conflict[j]=true;
            }
            std::vector<int> repaired;
            for(size_t i=0;i<raw.size();i++){
                repaired.push_back(raw[i]);
                if(!i || i+1==raw.size() || !conflict[i])continue;
                if(std::popcount(unsigned(raw[i-1]^raw[i+1]))!=2)continue;
                repaired.push_back(raw[i-1]^raw[i]^raw[i+1]);
            }
            raw=std::move(repaired);
        }
        ++count;int n=int(raw.size());after.assign(n,{});upper.assign(n,1);
        for(int i=n-1;i>=0;i--)for(int j=i+1;j<n;j++)
            if(std::popcount(unsigned(raw[i]^raw[j]))==1){
                after[i].push_back(j);upper[i]=std::max(upper[i],1+upper[j]);
            }
        for(int i=0;i<n;i++)if(upper[i]+2*radius>=target+1)walk(i,{});
    }
    std::cout<<"cases "<<count<<" nodes "<<nodes<<" cores "<<cores<<" best_seen_edges "
             <<(best.empty()?-1:int(best.size()-1))<<std::endl;
    if(!best.empty()){std::cout<<"BEST";for(int v:best)std::cout<<" "<<v;std::cout<<std::endl;}
}
