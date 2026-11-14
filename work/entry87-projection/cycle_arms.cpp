// Solve the exact two-end extension problem on each surviving arc of a coil.
// Usage: cycle-arms first-k last-k call-budget-per-removed-length < candidate.txt
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;

bool induced(const vector<int>& v,bool cycle=false){
    for(size_t j=0;j<v.size();j++)for(size_t i=0;i<j;i++){
        int d=popcount(unsigned(v[i]^v[j]));
        bool edge=j==i+1 || (cycle && i==0 && j+1==v.size());
        if(edge?d!=1:d<2)return false;
    }
    return true;
}
struct Extension {
    array<unsigned char,512> occupied{};
    vector<int> base,left,right,witness;
    int target,best=0;
    uint64_t& nodes;
    uint64_t limit;
    bool exhausted=true;
    Extension(vector<int> p,int desired,uint64_t& count,uint64_t cap):
        base(std::move(p)),target(desired),nodes(count),limit(cap){
        for(int x:base)add(x,1);
    }
    void add(int v,int step){
        occupied[v]+=step;
        for(int b=0;b<9;b++)occupied[v^(1<<b)]+=step;
    }
    bool stop(){
        if(!witness.empty())return true;
        if(nodes>=limit){exhausted=false;return true;}
        return false;
    }
    void extendRight(int head){
        if(stop())return;
        ++nodes;
        int count=base.size()+left.size()+right.size();
        best=max(best,count);
        if(count==target){
            witness.assign(left.rbegin(),left.rend());
            witness.insert(witness.end(),base.begin(),base.end());
            witness.insert(witness.end(),right.begin(),right.end());
            if(!induced(witness))throw logic_error("invalid candidate");
            return;
        }
        for(int b=0;b<9;b++){
            int y=head^(1<<b);
            if(occupied[y]!=1)continue;
            add(y,1);right.push_back(y);extendRight(y);right.pop_back();add(y,-1);
            if(stop())return;
        }
    }
    void extendLeft(int head){
        extendRight(base.back());
        if(stop())return;
        for(int b=0;b<9;b++){
            int y=head^(1<<b);
            if(occupied[y]!=1)continue;
            add(y,1);left.push_back(y);extendLeft(y);left.pop_back();add(y,-1);
            if(stop())return;
        }
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int start=stoi(argv[1]),end=stoi(argv[2]);
    uint64_t limit=stoull(argv[3]);
    vector<int> q;
    for(int v;cin>>v;)q.push_back(v);
    if(q.size()!=193)return 3;
    vector<int> cycle(q.begin()+7,q.end());
    if(!induced(cycle,true))throw logic_error("invalid source cycle");
    int n=cycle.size();
    if(start<1||end>=n-1||start>end)return 4;
    cout<<"removed,complete_cuts,nodes,max_vertices,found,witness\n";
    for(int k=start;k<=end;k++){
        uint64_t nodes=0;
        int cuts=0,best=0;
        vector<int> hit;
        for(int cut=0;cut<n;cut++){
            vector<int> p;
            for(int j=k;j<n;j++)p.push_back(cycle[(cut+j)%n]);
            Extension s(std::move(p),193,nodes,limit);
            s.extendLeft(s.base.front());
            best=max(best,s.best);
            if(!s.witness.empty()){hit=s.witness;break;}
            if(!s.exhausted)break;
            cuts++;
        }
        cout<<k<<','<<cuts<<','<<nodes<<','<<best<<','<<!hit.empty()<<',';
        for(int v:hit)cout<<v<<' ';
        cout<<endl;
        if(!hit.empty())return 0;
    }
}
