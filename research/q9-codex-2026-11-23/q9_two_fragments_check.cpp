#define Q9_FRAGMENT_LIBRARY
#include "q9_two_fragments.cpp"
#include <sstream>
#include <map>
using Path=vector<int>;
struct SmallOracle{
    vector<Path> records;
    vector<pair<uint32_t,int>> all;
    void walk(Path& v,uint32_t occupied){
        int n=v.size();
        all.emplace_back(occupied,n-1);
        if(n>=5 && v.front()==0)records.push_back(v);
        for(int b=0;b<4;b++){
            int x=v.back()^(1<<b);if((occupied>>x)&1)continue;
            bool chord=false;
            for(int j=0;j<n-1;j++)if(popcount(unsigned(x^v[j]))==1)chord=true;
            if(chord)continue;
            v.push_back(x);walk(v,occupied|(1u<<x));v.pop_back();
        }
    }
};
int main(){
    SmallOracle oracle;
    for(int x=0;x<16;x++){Path v{x};oracle.walk(v,1u<<x);}
    sort(oracle.all.begin(),oracle.all.end());oracle.all.erase(unique(oracle.all.begin(),oracle.all.end()),oracle.all.end());
    // Cache the independently enumerated maximum for each set of mandatory points.
    map<uint32_t,int> maximum;
    uint64_t positive=0,negative=0;
    struct Silent:streambuf{int overflow(int c)override{return c;}} silent;
    auto old=cout.rdbuf(&silent);
    for(auto& v:oracle.records)for(int l=0;l<=1;l++)for(int r=0;r<=1;r++)
        for(int g=1;g<=3;g++)for(int i=l+1;i+g+2<int(v.size())-r;i++){
            bool translate=std::getenv("Q9_TRANSLATE");
            int expectedBest=0;
            vector<pair<int,int>> swaps{{0,0}};
            bool swapAxes=std::getenv("Q9_AXIS_SWAP");
            if(swapAxes)for(int a=0;a<4;a++)for(int b=a+1;b<4;b++)swaps.emplace_back(a,b);
            for(auto [a,b]:swaps)for(int t=0;t<(translate?16:1);t++){
                uint32_t left=0,right=0;
                for(int k=l;k<=i;k++)left|=1u<<v[k];
                for(int k=i+g+1;k<int(v.size())-r;k++){
                    int x=v[k];
                    if(((x>>a)^(x>>b))&1)x^=(1<<a)|(1<<b);
                    right|=1u<<(x^t);
                }
                if(left&right)continue;
                uint32_t need=left|right;
                if(!maximum.count(need)){
                    int best=0;
                    for(auto [mask,n]:oracle.all)if((mask&need)==need)best=max(best,n);
                    maximum[need]=best;
                }
                expectedBest=max(expectedBest,maximum.at(need));
            }
            for(int target=6;target<=8;target++){
                JoinSearch s;s.extension.dimensions=4;s.extension.goal=target;s.translate=translate;s.swapAxes=swapAxes;
                bool expected=expectedBest>=target;
                if(s.run(v,l,r,i,g)!=expected)throw runtime_error("oracle disagreement");
                if(expected)positive++;else negative++;
            }
        }
    cout.rdbuf(old);
    cout<<"MATCH "<<positive<<" "<<negative<<" "<<maximum.size()<<" "<<oracle.all.size()<<endl;
}
