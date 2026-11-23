// Embed a path around both copies of a Q8 cycle, changing the layer along each lap.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
bool valid(const Path&p,int dim,bool cyclic){
    for(int i=0;i<int(p.size());i++){
        if(p[i]<0||p[i]>=(1<<dim))return false;
        for(int j=0;j<i;j++){
            int d=popcount(unsigned(p[i]^p[j]));
            if(!d||(d==1)!=(j+1==i||(cyclic&&j==0&&i+1==p.size())))return false;
        }
    }
    return true;
}
struct Solver{
    int target,n,limit; uint64_t nodes=0,cap;
    array<int,512> blocked{};Path p,best,answer;vector<int> cycle;
    bool step(int index,int dir,int edits){
        if(p.size()>best.size())best=p;
        if(int(p.size())==target+1){if(!valid(p,9,false))abort();answer=p;return true;}
        if(nodes>=cap)return false;nodes++;
        int tip=p.back(),lower=tip&255,layer=tip&256;
        auto take=[&](int x,int j,int sign,int nextEdits){
            if(blocked[x])return false;
            p.push_back(x);blocked[tip]++;
            for(int d=0;d<9;d++)blocked[tip^(1<<d)]++;
            bool found=step(j,sign,nextEdits);
            for(int d=0;d<9;d++)blocked[tip^(1<<d)]--;
            blocked[tip]--;p.pop_back();return found;
        };
        // A monotone lap with an optional layer flip (cost is counted only for deviations).
        int j=(index+dir+n)%n;
        if(index>=0 && take(layer+cycle[j],j,dir,edits))return true;
        if(index>=0 && take(tip^256,index,dir,edits))return true;
        if(edits<limit){
            if(index>=0){
                int h=(index-dir+n)%n;
                if(take(layer+cycle[h],h,-dir,edits+1))return true;
            }
            for(int d=0;d<9;d++){
                int x=tip^(1<<d);
                auto pos=find(cycle.begin(),cycle.end(),x&255);
                int h=pos==cycle.end()?-1:int(pos-cycle.begin());
                if(index>=0 && (h==j||h==index||h==(index-dir+n)%n))continue;
                if(take(x,h,dir,edits+1))return true;
                if(h>=0&&index<0&&take(x,h,-dir,edits+1))return true;
            }
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;int id=0;string w;
    while(cin>>w){
        Solver s;s.target=stoi(argv[1]);s.limit=stoi(argv[2]);s.cap=stoull(argv[3]);s.cycle={0};
        for(char c:w)s.cycle.push_back(s.cycle.back()^1<<(c-'0'));
        if(s.cycle.back())return 3;s.cycle.pop_back();s.n=s.cycle.size();
        if(!valid(s.cycle,8,true))return 4;
        for(int i=0;i<s.n&&s.nodes<s.cap&&s.answer.empty();i++)for(int dir:{-1,1}){
            s.p={s.cycle[i]};if(s.step(i,dir,0))break;
        }
        if(!valid(s.best,9,false))abort();
        cout<<id++<<" "<<(s.answer.empty()?(s.nodes>=s.cap?"UNKNOWN":"EXHAUSTED"):"FOUND")<<" "<<s.nodes<<" "<<s.best.size()-1;
        for(int v:s.best)cout<<" "<<v;cout<<endl;
    }
}
