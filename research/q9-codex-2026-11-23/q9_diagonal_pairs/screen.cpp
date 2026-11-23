// Quotient by translating by a weight-at-least-three vector, retaining the occupied pairs.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
int main(){
    int row=0;
    for(string w;cin>>w;++row){
        vector<int> path{0};for(char d:w)path.push_back(path.back()^(1<<(d-'0')));
        for(int m=1;m<512;++m){
            if(popcount(unsigned(m))<3)continue;
            auto rep=[&](int x){return min(x,x^m);};
            array<int,512> count{},deg{};int nc=0,eligible=0;
            for(int v:path)if(++count[rep(v)]==1)++nc;
            vector<int> candidates;
            for(int u=0;u<512;++u)if(count[u]){
                for(int d=0;d<9;++d)deg[u]+=count[rep(u^(1<<d))]!=0;
                if(deg[u]<=4){++eligible;candidates.push_back(u);}
                else if(count[u]==2)return 2;
            }
            int parityCap=nc+eligible;
            if(popcount(unsigned(m))%2==0){
                int cap[2]{};
                for(int v=0;v<512;++v)if(count[v])cap[popcount(unsigned(v))&1]+=1+(deg[v]<=4);
                parityCap=min(parityCap,2*min(cap[0],cap[1])+1);
            }
            cout<<row<<' '<<m<<' '<<nc<<' '<<eligible<<' '<<parityCap<<'\n';
        }
    }
}
