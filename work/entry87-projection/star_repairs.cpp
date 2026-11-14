// Toggle one arbitrary address and at most two closed neighbourhoods.
// The necessary degree pruning checks the induced graph on the whole cube.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <vector>
using namespace std;

#include "star_board.hpp"

int main(){
    int d,target,limit,records;
    if(!(cin>>d>>target>>limit>>records)||d<1||d>9||limit<0||limit>2) return 2;
    for(int index=0;index<records;index++){
        Board board(d); int count; cin>>count;
        for(int i=0,v;i<count;i++){cin>>v;board.toggle(v);}
        array<long long,3> classes{},candidates{},degree_models{},solutions{};
        vector<int> first; array<int,3> change{-1,-1,-1};
        auto decide=[&](int a,int b,int k){
            ++classes[k];
            if(abs(target-board.size)!=1||board.bad>d+1||abs(board.tips-2)>d+1) return;
            int bad=0;
            while(bad<board.n&&(!board.used[bad]||(board.degree[bad]==1||board.degree[bad]==2))) ++bad;
            const int count_v=bad<board.n?d+1:board.n;
            for(int j=0;j<count_v;j++){
                int v=bad<board.n?board.ball[bad][j]:j;
                if(board.size+(board.used[v]?-1:1)!=target) continue;
                ++candidates[k];board.toggle(v);
                if(!board.bad&&board.tips==2){
                    ++degree_models[k];auto q=board.path();
                    if(!q.empty()){
                        ++solutions[k];
                        if(first.empty()){first=q;change={v,a,b};}
                    }
                }
                board.toggle(v);
            }
        };
        decide(-1,-1,0);
        if(limit>=1) for(int a=0;a<board.n;a++){
            board.star(a); decide(a,-1,1);
            if(limit==2) for(int b=a+1;b<board.n;b++){
                board.star(b);decide(a,b,2);board.star(b);
            }
            board.star(a);
        }
        cout<<index;
        for(const auto &x:{classes,candidates,degree_models,solutions}) for(auto v:x) cout<<' '<<v;
        for(int v:change) cout<<' '<<v;
        cout<<' '<<first.size();for(int v:first) cout<<' '<<v;
        cout<<endl;
    }
}
