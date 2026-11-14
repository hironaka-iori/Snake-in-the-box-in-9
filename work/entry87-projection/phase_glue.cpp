// Try two translated copies of an induced 96-edge path, with permuted second copy.
// Input is one rooted canonical 97-vertex path per line. Output gives exact counts.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;

struct Path{
    array<int,97> vertex{};
    array<int,97> move{};
    array<int,512> conflicts{};
    explicit Path(const array<int,97>& q):vertex(q){
        if(q[0]!=0)throw invalid_argument("root");
        for(int j=0;j<97;++j){
            if(q[j]<0 || q[j]>=512)throw invalid_argument("word");
            if(j)move[j]=countr_zero(unsigned(q[j]^q[j-1]));
            for(int i=0;i<j;++i){
                int h=popcount(unsigned(q[i]^q[j]));
                if(j==i+1?h!=1:h<2)throw invalid_argument("input");
            }
            if(j<96){
                ++conflicts[q[j]];
                for(int b=0;b<9;++b)++conflicts[q[j]^(1<<b)];
            }
        }
    }
};

int main(){
    string line;
    while(getline(cin,line)){
        istringstream in(line);
        array<int,97> q;
        for(int& v:q)if(!(in>>v))return 2;
        Path path(q);
        int best=100000;
        int multiplicity=0;
        array<int,9> winner{},perm{0,1,2,3,4,5,6,7,8};
        do{
            int sum=0,vertex=q.back();
            for(int j=1;j<97;++j){
                vertex^=1<<perm[path.move[j]];
                sum+=path.conflicts[vertex];
                if(sum>best)break;
            }
            if(sum<best){best=sum;winner=perm;multiplicity=0;}
            if(sum==best)++multiplicity;
        }while(next_permutation(perm.begin(),perm.end()));
        cout<<best<<' '<<multiplicity;
        for(int b:winner)cout<<' '<<b;
        cout<<'\n';
        if(best==0){
            int vertex=q.back();
            cout<<"witness";
            for(int z:q)cout<<' '<<z;
            for(int j=1;j<97;++j){vertex^=1<<winner[path.move[j]];cout<<' '<<vertex;}
            cout<<'\n';
            return 0;
        }
        cout.flush();
    }
    return 0;
}
