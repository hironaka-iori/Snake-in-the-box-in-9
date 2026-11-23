#define Q9_VARIABLE_FOREST_LIBRARY
#include "search_q9_variable_projected_forest.cpp"
int main(){
    // Independent enumeration of every oriented induced path of Q4.
    vector<Path> all;Path path;
    auto extend=[&](auto&& self)->void{
        all.push_back(path);for(int bit=1;bit<16;bit*=2){
            int x=path.back()^bit;bool ok=true;
            for(int j=0;j+1<path.size();j++)if(popcount(unsigned(x^path[j]))<=1)ok=false;
            if(ok){path.push_back(x);self(self);path.pop_back();}
        }
    };
    for(int i=0;i<16;i++){path={i};extend(extend);}
    mt19937 rng(623660);int yes=0,no=0;
    for(int sample=0;sample<600;sample++){
        Path a,b;
        while(true){
            auto &x=all[rng()%all.size()],&y=all[rng()%all.size()];
            if(x.size()<2||y.size()<2)continue;
            int na=2+rng()%2,nb=2+rng()%2;if(na>x.size()||nb>y.size())continue;
            a.assign(x.begin(),x.begin()+na);b.assign(y.begin(),y.begin()+nb);
            bool ok=true;for(int i:a)for(int j:b)if(popcount(unsigned(i^j))<=1)ok=false;if(ok)break;
        }
        int target=4+rng()%6;bool oracle=false;
        for(auto &p:all)if(p.size()>target){
            auto i=std::search(p.begin(),p.end(),a.begin(),a.end());if(i==p.end())continue;
            auto j=std::search(i+a.size(),p.end(),b.begin(),b.end());if(j!=p.end()){oracle=true;break;}
        }
        Join join({a,b},target,1000000,15);bool found=join.next(0);
        assert(!join.cutoff&&found==oracle);yes+=found;no+=!found;
    }
    cout<<"Q4_oriented_paths "<<all.size()<<" fixed_order_comparisons "<<yes+no<<" yes "<<yes<<" no "<<no<<endl;
}
