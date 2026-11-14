// Five touching shapes and their isometry orbit on every three-bit projection.
// Reads the 131 ordered 191-edge snakes, one row per seed, as whitespace-separated vertices.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
using Score=array<int,24>;
using PairScores=array<Score,2>;

int main(){
    array<int,5> init{1<<2,1<<3,(1<<0)|(1<<1),(1<<0)|(1<<7),(1<<1)|(1<<6)};
    array<int,3> permutation{0,1,2};
    set<array<int,5>> orbit;
    do {
        for(int off=0;off<8;off++){
            array<int,5> f{};
            for(int k=0;k<5;k++) for(int x=0;x<8;x++) if(init[k]>>x&1){
                int y=off;for(int i=0;i<3;i++)y^=((x>>i)&1)<<permutation[i];
                f[k]|=1<<y;
            }
            sort(f.begin(),f.end());orbit.insert(f);
        }
    }while(next_permutation(permutation.begin(),permutation.end()));
    if(orbit.size()!=24)throw logic_error("shape orbit");
    array<Score,256> covers{};
    int family=0;
    for(auto f:orbit){
        for(int trace=1;trace<256;trace++)
            covers[trace][family]=any_of(f.begin(),f.end(),[=](int s){return (s&trace)==s;});
        family++;
    }
    cout<<"entry,retained_mask,exclusions,peak,sample_position,sample_parity,sample_family,excluded_positions\n";
    for(int seed=0;seed<131;seed++){
        array<int,192> input{};
        for(int& x:input)if(!(cin>>x))throw invalid_argument("missing path");
        for(int mask=0;mask<512;mask++)if(popcount(unsigned(mask))==3){
            array<int,192> z{},id{},left{},right{};
            vector<int> trace(1,0);
            array<int,3> keep{};int k=0;
            for(int b=0;b<9;b++)if(mask>>b&1)keep[k++]=b;
            for(int j=0;j<192;j++){
                for(int b=0;b<3;b++)z[j]|=((input[j]>>keep[b])&1)<<b;
                if(j && z[j-1]==z[j])trace.push_back(0);
                id[j]=int(trace.size())-1;trace.back()|=1<<z[j];
                left[j]=((j && id[j-1]==id[j])?left[j-1]:0)|(1<<z[j]);
            }
            for(int j=191;j>=0;j--)
                right[j]=((j<191 && id[j+1]==id[j])?right[j+1]:0)|(1<<z[j]);
            vector<PairScores> prefix(trace.size()+1);
            for(size_t r=0;r<trace.size();r++){
                prefix[r+1]=prefix[r];
                for(int f=0;f<24;f++)prefix[r+1][r%2][f]+=covers[trace[r]][f];
            }
            int excluded=0,peak=0,position=0,parity=0,which=0;
            vector<int> excludedPositions;
            for(int j=0;j<192;j++){
                int r=id[j],p=r%2,best=0;
                for(int f=0;f<24;f++)for(int a=0;a<2;a++){
                    int score=prefix[r][a][f]+
                        (prefix.back()[1-a][f]-prefix[r+1][1-a][f])+
                        (a==p?covers[left[j]][f]:covers[right[j]][f]);
                    best=max(best,score);
                    if(score>peak){peak=score;position=j;parity=a;which=f;}
                }
                if(best>32){excluded++;excludedPositions.push_back(j);}
            }
            cout<<seed<<','<<mask<<','<<excluded<<','<<peak<<','<<position<<','<<parity<<','<<which<<',';
            for(size_t h=0;h<excludedPositions.size();h++)cout<<(h?" ":"")<<excludedPositions[h];
            cout<<'\n';
        }
    }
}
