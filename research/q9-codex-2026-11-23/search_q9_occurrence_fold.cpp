// For a fixed source direction, independently choose its image on every occurrence.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Search {
    vector<int> steps, path, best;
    array<int,512> used{}, touches{};
    int target=192, start=0, hidden=0, second=-1;
    uint64_t nodes=0, budget=0;
    bool hit=false, cutoff=false;
    void mark(int v,int sign) {
        used[v]+=sign;
        for(int d=0;d<9;++d) touches[v^(1<<d)]+=sign;
    }
    void dfs(int t) {
        if(hit || cutoff) return;
        if(++nodes>budget) {cutoff=true;return;}
        if(path.size()>best.size()) best=path;
        if(int(path.size())>target) {hit=true;return;}
        if(int(path.size())-1+int(steps.size())-t<target)return;
        int a=steps[t];
        if(a==hidden || a==second) dfs(t+1);
        int pinned=a-(a>hidden)-(second>=0 && a>second);
        for(int d=0;d<9 && !hit && !cutoff;++d) {
            if(a!=hidden && a!=second && d!=pinned)continue;
            int v=path.back()^(1<<d);
            if(used[v] || touches[v]!=1)continue;
            mark(v,1);path.push_back(v);dfs(t+1);path.pop_back();mark(v,-1);
        }
    }
};
bool valid(const vector<int>& p,int dim) {
    for(int j=0;j<int(p.size());++j){
        if(p[j]<0 || p[j]>=(1<<dim))return false;
        for(int i=0;i<j;++i)
            if(p[i]==p[j] || ((__builtin_popcount(unsigned(p[i]^p[j]))==1)!=(i+1==j)))return false;
    }return true;
}
int main(int argc,char** argv) {
    if(argc!=4)return 2;
    int hiddenCount=stoi(argv[1]),target=stoi(argv[2]);
    uint64_t budget=stoull(argv[3]);
    string line;
    for(int row=0;getline(cin,line);++row) {
        istringstream in(line);int dim,a;in>>dim;if(dim!=10)return 2;
        vector<int> word,source{0};
        while(in>>a){if(a<0||a>=dim)return 2;word.push_back(a);source.push_back(source.back()^(1<<a));}
        if(!valid(source,dim))return 3;
        for(int h=0;h<10;++h)for(int k=(hiddenCount==1?-1:h+1);k<(hiddenCount==1?0:10);++k) {
            Search s;s.steps=word;s.hidden=h;s.second=k;s.target=target;s.budget=budget;
            s.mark(0,1);s.path={0};
            uint64_t total=0;int cuts=0,starts=0;
            for(s.start=0;s.start+target<=int(word.size())&&!s.hit;++s.start) {
                s.cutoff=false;s.nodes=0;s.dfs(s.start);total+=s.nodes;cuts+=s.cutoff;++starts;
            }
            if(!valid(s.best,9))return 4;
            cout<<"{\"row\":"<<row<<",\"axes\":["<<h;
            if(k>=0)cout<<","<<k;
            cout<<"],\"starts\":"<<starts<<",\"nodes\":"<<total<<",\"cutoffs\":"<<cuts<<",\"best\":"<<int(s.best.size())-1;
            if(s.hit){cout<<",\"vertices\":[";for(size_t j=0;j<s.best.size();++j)cout<<(j?",":"")<<s.best[j];cout<<"]";}
            cout<<"}"<<endl;if(s.hit)return 0;
        }
    }
}
