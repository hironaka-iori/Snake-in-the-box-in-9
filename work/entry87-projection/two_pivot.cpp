// Independently rotate both end segments about two fixed hinges of an induced middle.
// Usage: two_pivot first-left-pivot last-left-pivot max-right-arm < candidate.txt
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
using Perm=array<int,9>;

int permute(int w,const Perm& p) {
    int t=0;
    for(unsigned z=w;z;z&=z-1) t|=1<<p[countr_zero(z)];
    return t;
}
bool induced(const vector<int>& p){
    for(size_t j=0;j<p.size();j++)for(size_t i=0;i<j;i++){
        int d=popcount(unsigned(p[i]^p[j]));
        if(j==i+1?d!=1:d<2)return false;
    }
    return true;
}
using Layout=vector<int>;
struct ArmOptions { int raw=0; vector<Perm> representatives; };

ArmOptions options(const vector<int>& core,const vector<int>& arm,int hinge) {
    array<bool,512> bad{};
    for(int w:core)if(w!=hinge){
        bad[w]=true;
        for(int b=0;b<9;b++)bad[w^(1<<b)]=true;
    }
    vector<int> offsets;
    for(int v:arm)if(v!=hinge)offsets.push_back(v^hinge);
    Perm p{0,1,2,3,4,5,6,7,8};
    ArmOptions out;
    set<Layout> seen;
    do{
        bool ok=true;
        for(int w:offsets)if(bad[hinge^permute(w,p)]){ok=false;break;}
        if(!ok)continue;
        out.raw++;
        Layout support;
        for(int w:offsets)support.push_back(hinge^permute(w,p));
        sort(support.begin(),support.end());
        if(seen.insert(support).second)out.representatives.push_back(p);
    }while(next_permutation(p.begin(),p.end()));
    return out;
}
int main(int argc,char**argv){
    if(argc!=4)return 2;
    vector<int> q;
    for(int w;cin>>w;)q.push_back(w);
    if(q.size()!=193)return 3;
    const int start=stoi(argv[1]),stop=stoi(argv[2]),maxright=stoi(argv[3]);
    cout<<"left_pivot,right_pivot,left_raw,left_sets,right_raw,right_sets,valid,witness\n";
    for(int i=start;i<=stop;i++)for(int j=max(i+1,192-maxright);j<=191;j++){
        vector<int> a(q.begin(),q.begin()+i+1),m(q.begin()+i,q.begin()+j+1),b(q.begin()+j,q.end());
        if(!induced(a)||!induced(m)||!induced(b))continue;
        auto A=options(m,a,q[i]),B=options(m,b,q[j]);
        int valid=0;
        vector<int> witness;
        for(const auto& pa:A.representatives){
            array<bool,512> bad{};
            for(int k=0;k<i;k++){
                int w=q[i]^permute(q[i]^q[k],pa);
                bad[w]=true;
                for(int bit=0;bit<9;bit++)bad[w^(1<<bit)]=true;
            }
            for(const auto& pb:B.representatives){
                bool ok=true;
                for(int k=j+1;k<193;k++)if(bad[q[j]^permute(q[j]^q[k],pb)]){ok=false;break;}
                if(!ok)continue;
                ++valid;
                if(witness.empty()){
                    witness=q;
                    for(int k=0;k<i;k++)witness[k]=q[i]^permute(q[i]^q[k],pa);
                    for(int k=j+1;k<193;k++)witness[k]=q[j]^permute(q[j]^q[k],pb);
                    if(!induced(witness))throw logic_error("verification");
                }
            }
        }
        cout<<i<<','<<j<<','<<A.raw<<','<<A.representatives.size()<<','
            <<B.raw<<','<<B.representatives.size()<<','<<valid<<',';
        for(int w:witness)cout<<w<<' ';
        cout<<'\n';
        if(valid)return 0;
    }
}
