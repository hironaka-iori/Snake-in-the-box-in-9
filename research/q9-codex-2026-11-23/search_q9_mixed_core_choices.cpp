#define Q9_CORNER_DRIVER
#include "search_q9_corners_and_tips.cpp"
#include <random>
int main(int argc,char**argv){
    if(argc!=5)return 2;int trials=stoi(argv[1]),batchseed=stoi(argv[2]),target=stoi(argv[3]),budget=stoi(argv[4]);mt19937 rng(batchseed);
    vector<Path> bank;string word;
    while(cin>>word){
        Path p{0};for(char d:word)p.push_back(p.back()^(1<<(d-'0')));
        assert(p.size()==192&&valid(p));bank.push_back(p);
    }
    uint64_t nodes=0,tests=0,caps=0;int maxVar=0;
    for(int h=0;h<trials;h++){
        int id=rng()%bank.size();auto& p=bank[id];
        int trim=rng()%34,a=rng()%(trim+1),b=trim-a;
        Path core(p.begin()+a,p.end()-b),alt=core;
        int n=core.size(),blocks=1+rng()%5;
        for(int k=0;k<blocks;k++){
            int left=k*n/blocks,right=(k+1)*n/blocks;
            int x=rng()%9,y=(x+1+rng()%8)%9,m=(1<<x)^(1<<y);
            int form=rng()%4,anchor=core[left+rng()%(right-left)];
            for(int i=max(1,left);i<min(right,n-1);i++){
                int q=core[i];
                if(form==0)alt[i]=q^m;
                if(form==1)alt[i]=popcount(unsigned((q^anchor)&m))==1?q^m:q;
                if(form==2)alt[i]=core[i-1]^q^core[i+1];
                if(form==3)alt[i]=(q&(1<<x))==(anchor&(1<<x))?q^m:q;
            }
        }
        Engine model(core,budget,-1,alt);maxVar=max(maxVar,model.corners);
        int ext=target+1-core.size();for(int l=0;l<=ext;l++){
            model.nodes=0;model.cutoff=false;tests++;
            if(model.visit(l,ext-l,Forced{})){cout<<"FOUND "<<id<<" "<<a<<" "<<b<<" "<<l;
                for(int x:model.witness)cout<<" "<<x;cout<<endl;return 0;}
            nodes+=model.nodes;caps+=model.cutoff;
        }
    }
    cout<<"DONE "<<trials<<" "<<tests<<" "<<caps<<" "<<nodes<<" "<<maxVar<<endl;
}
