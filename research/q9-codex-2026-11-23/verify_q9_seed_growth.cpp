#include "q9_seed_growth.hpp"
#include <iostream>
#include <random>
using namespace std;
bool brute(vector<int>a,vector<int>b,int dim,int target,int e,int retain=-1){
    int S=0;for(auto p:{a,b})for(int x:p)S|=1<<x;
    auto go=[&](auto&& self,int mask,int last,int len)->bool{
        if(popcount(unsigned(mask&~S))>e)return false;
        if(len>=target&&popcount(unsigned(mask&S))>=retain)return true;
        for(int j=0;j<dim;j++){int y=last^(1<<j);if(mask&(1<<y))continue;
            int hits=0;for(int k=0;k<dim;k++)if(mask&(1<<(y^(1<<k))))hits++;
            if(hits==1&&self(self,mask|(1<<y),y,len+1))return true;
        }return false;
    };
    for(int x=0;x<(1<<dim);x++)if(go(go,1<<x,x,0))return true;
    return false;
}
int main(){
    mt19937 rng(84357);
    for(int dim=3;dim<=4;dim++)for(int e=0;e<=5;e++){
        int positive=0;
        for(int i=0;i<1000;i++){
            auto draw=[&](int high){
                vector<int>p{int(rng()%(1<<(dim-1)))+high};
                int goal=1+rng()%6;
                while(p.size()<goal){vector<int> opts;
                    for(int d=0;d<dim-1;d++){int x=p.back()^(1<<d);
                        if(find(p.begin(),p.end(),x)!=p.end())continue;
                        int z=0;for(int y:p)z+=has_single_bit(unsigned(x^y));if(z==1)opts.push_back(x);
                    }
                    if(opts.empty())break;p.push_back(opts[rng()%opts.size()]);
                }return p;
            };
            auto a=draw(0),b=draw(1<<(dim-1));int target=2+rng()%8;
            int retained=-1,allow=e;
#ifdef Q9_CHECK_RETAINED
            retained=rng()%(int(a.size()+b.size())+1);allow=(1<<dim)-int(a.size()+b.size());
#endif
            bool actual=brute(a,b,dim,target,allow,retained);SeedGrow test;
            if(test.run(a,b,dim,target,allow,retained)!=actual)abort();positive+=actual;
        }cout<<"MATCH "<<dim<<" "<<e<<" 1000 "<<positive<<endl;
    }
}
