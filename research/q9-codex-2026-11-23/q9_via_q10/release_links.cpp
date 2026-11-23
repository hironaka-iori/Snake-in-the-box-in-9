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
using namespace std;
using Path=vector<int>;
array<Path,512> shell;
int midpoint(int x,int y,const array<unsigned char,512>& load){
    int mask=x^y,a=mask&-mask,b=mask^a;
    if(!a || !has_single_bit(unsigned(b)))return -1;
    return load[x^a]==2?(x^a):load[x^b]==2?(x^b):-1;
}
struct Problem{
    Path seq,original;array<unsigned char,512> used{},load{};
    bool odd=false;int visits=0,limit;mt19937& rng;Path result;
    Problem(Path p,bool o,int cap,mt19937& r):seq(p.size(),-1),original(p),odd(o),limit(cap),rng(r){}
    void place(int i,int x,int d){
        if(d==1){assert(!used[x]);seq[i]=x;}else{assert(used[x]);seq[i]=-1;}
        used[x]+=d;for(int b=1;b<512;b*=2)load[x^b]+=d;
    }
    bool ok()const{
        for(int i=1;i<int(seq.size());i++)if(seq[i]>=0 && seq[i-1]>=0 && midpoint(seq[i],seq[i-1],load)<0)return false;
        if(odd && seq.back()>=0){
            for(int b=1;b<512;b*=2)if(load[seq.back()^b]==1)return true;
            return false;
        }
        return true;
    }
    bool search(){
        if(++visits>limit || !ok())return false;
        int slot=-1;Path candidates;
        for(int i=0;i<int(seq.size());i++)if(seq[i]<0){
            int x=i?seq[i-1]:-1,y=i+1<int(seq.size())?seq[i+1]:-1;
            if(x<0)swap(x,y);if(x<0)continue;
            Path local;
            for(int v:shell[x])if(!used[v] && (y<0 || popcount(unsigned(v^y))==2)){
                place(i,v,1);bool fit=ok();place(i,v,-1);if(fit)local.push_back(v);
            }
            if(local.empty())return false;
            if(slot<0 || local.size()<candidates.size()){slot=i;candidates=move(local);}
        }
        if(slot<0){
            if(find(seq.begin(),seq.end(),-1)!=seq.end())return false;
            result={seq[0]};for(int i=1;i<int(seq.size());i++){
                result.push_back(midpoint(seq[i-1],seq[i],load));result.push_back(seq[i]);}
            if(odd)for(int b=1;b<512;b*=2)if(load[seq.back()^b]==1){result.push_back(seq.back()^b);break;}
            for(int j=0;j<int(result.size());j++)for(int i=0;i<j;i++){
                int dist=popcount(unsigned(result[i]^result[j]));assert(dist>0 && (dist==1)==(i+1==j));
            }
            return true;
        }
        shuffle(candidates.begin(),candidates.end(),rng);
        auto it=find(candidates.begin(),candidates.end(),original[slot]);if(it!=candidates.end())iter_swap(it,candidates.begin());
        for(int v:candidates){place(slot,v,1);if(search())return true;place(slot,v,-1);if(visits>=limit)break;}
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=6)return 2;
    ifstream in(argv[1]);int rounds=stoi(argv[2]),cap=stoi(argv[3]);mt19937 rng(stoul(argv[4]));bool odd=stoi(argv[5]);string line;vector<Path> bank;
    for(int v=0;v<512;v++)for(int a=1;a<512;a*=2)for(int b=a*2;b<512;b*=2)shell[v].push_back(v^a^b);
    while(getline(in,line)){istringstream row(line);Path p;int x,t=0;while(row>>x){if(t++%2==0)p.push_back(x);}if(!p.empty())bank.push_back(p);}
    if(bank.empty())return 2;
    uint64_t done=0,limited=0,feasible=0,visited=0;
    for(int job=0;job<rounds;job++){
        const Path& p=bank[rng()%bank.size()];Problem s(p,odd,cap,rng);for(int i=0;i<int(p.size());i++)s.place(i,p[i],1);
        vector<int> bad;
        for(int i=1;i<int(p.size());i++)if(midpoint(p[i-1],p[i],s.load)<0){
            vector<int> culprits{i-1,i};int z=p[i]^p[i-1],a=z&-z,b=z^a;
            for(int j=0;j<int(p.size());j++)if(j!=i && j!=i-1){
                if(popcount(unsigned(p[j]^p[i]^a))==1||popcount(unsigned(p[j]^p[i]^b))==1)culprits.push_back(j);
            }
            shuffle(culprits.begin(),culprits.end(),rng);int num=1+rng()%min<int>(4,culprits.size());
            bad.insert(bad.end(),culprits.begin(),culprits.begin()+num);
        }
        if(odd)bad.push_back(p.size()-1);
        int extra=rng()%3;while(extra--)bad.push_back(rng()%p.size());
        vector<bool> freeSlot(p.size());
        for(int i:bad){int lo=rng()%4,hi=rng()%4;for(int j=max(0,i-lo);j<=min(int(p.size())-1,i+hi);j++)freeSlot[j]=true;}
        for(int i=0;i<int(p.size());i++)if(freeSlot[i])s.place(i,p[i],-1);
        if(!s.ok())continue;
        feasible++;bool found=s.search();visited+=s.visits;
        if(found){cout<<"FOUND "<<s.result.size()-1;for(int v:s.result)cout<<" "<<v;cout<<endl;return 0;}
        if(s.visits>=cap)limited++;else done++;
        if(feasible%1000==0)cout<<"AT "<<job<<" "<<feasible<<" "<<done<<" "<<limited<<" "<<visited<<endl;
    }
    cout<<"DONE "<<rounds<<" "<<feasible<<" "<<done<<" "<<limited<<" "<<visited<<endl;
}
