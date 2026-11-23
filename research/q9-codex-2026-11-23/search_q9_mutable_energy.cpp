// Minimize repeated or adjacent nonconsecutive positions at a fixed target length.
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Energy {
    array<int,512> count{},near{};
    int operator()(const vector<int>& w){
        vector<int> path{0};path.reserve(w.size()+1);
        int x=0,score=0;
        auto add=[&](int v,int s){count[v]+=s;for(int k=0;k<9;k++)near[v^(1<<k)]+=s;};
        add(0,1);
        for(int a:w){x^=1<<a;score+=count[x]*2+near[x]-1;path.push_back(x);add(x,1);}
        for(int v:path)add(v,-1);
        return score;
    }
};
struct Search {
    int t;mt19937 rng; Energy e;
    int randInt(int bound){return int(rng()%bound);}
    void edit(vector<int>& w){
        int i=randInt(t),j=randInt(t);if(i>j)swap(i,j);
        if(randInt(3)!=0)j=min(t-1,i+1+randInt(24));
        int a=randInt(9),b=(a+1+randInt(8))%9;
        switch(randInt(8)){
        case 0:case 1:case 2:w[i]=a;break;
        case 3:swap(w[i],w[j]);break;
        case 4:reverse(w.begin()+i,w.begin()+j+1);break;
        case 5:for(int k=i;k<=j;k++){if(w[k]==a)w[k]=b;else if(w[k]==b)w[k]=a;}break;
        case 6:rotate(w.begin()+i,w.begin()+j,w.begin()+j+1);break;
        default: rotate(w.begin()+i,w.begin()+i+1,w.begin()+j+1);break;
        }
    }
    void run(int id,vector<int> w,int tries,int cycles){
        vector<int>best=w;int record=e(w);
        auto log=[&](){cout<<id<<" "<<t<<" "<<record<<" ";for(int d:best)cout<<d;cout<<endl;};
        log();
        for(int r=0;r<cycles && record;r++){
            vector<int> q=(r%4==0)?w:best;
            int cost=e(q);
            for(int n=0;n<tries&&record;n++){
                vector<int> candidate=q;edit(candidate);if(q==candidate)continue;
                int val=e(candidate);
                double temp=0.16+(1.-double(n)/tries)*(r%3==0?1.6:0.85);
                if(val<=cost||generate_canonical<double,32>(rng)<exp((cost-val)/temp)){q.swap(candidate);cost=val;}
                if(cost<record){best=q;record=cost;log();}
            }
        }
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;int tries=stoi(argv[1]),cycles=stoi(argv[2]),seed=stoi(argv[3]),target=stoi(argv[4]);
    string l;while(getline(cin,l)){
        istringstream in(l);int i,t,j;in>>i>>t>>j;if(t!=target)continue;
        vector<int>w;int last,x;in>>last;while(in>>x){int v=x^last;assert(__builtin_popcount(unsigned(v))==1);w.push_back(__builtin_ctz(unsigned(v)));last=x;}
        Search s{t,mt19937(unsigned(seed+i))};s.run(i,w,tries,cycles);
    }
}
