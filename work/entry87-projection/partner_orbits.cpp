// Minimize intersections of all rooted placements of a Q8 path with forbidden sites.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
int main(){
    int root,size,classes,forbidden_count;
    if(!(cin>>root>>size>>classes>>forbidden_count)||root<0||root>255||size<2||size>256)return 2;
    array<int,256> forbidden{};
    for(int i=0;i<forbidden_count;++i){int x;cin>>x;forbidden.at(x)=1;}
    if(forbidden[root])return 2;
    for(int k=0;k<classes;++k){
        vector<int> moves(size-1);
        for(int& m:moves){if(!(cin>>m)||m<0||m>7)return 2;}
        array<int,8> p{0,1,2,3,4,5,6,7},winner{};
        int best=999,count=0;
        do{
            int x=root,score=0;
            for(int m:moves){x^=1<<p[m];score+=forbidden[x];if(score>best)break;}
            if(score<best){best=score;winner=p;count=0;}
            if(score==best)++count;
        }while(next_permutation(p.begin(),p.end()));
        cout<<best<<' '<<count;
        for(int m:winner)cout<<' '<<m;
        cout<<'\n';
    }
}
