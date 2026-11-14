// Fix the first two neighbouring seven-cube layers. Enumerate the third
// from its forced root and directly solve the fourth from each possible hinge.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
struct Set{uint64_t lo=0,hi=0;};
Set operator|(Set a,Set b){return {a.lo|b.lo,a.hi|b.hi};}
Set operator&(Set a,Set b){return {a.lo&b.lo,a.hi&b.hi};}
Set without(Set a,Set b){return {a.lo&~b.lo,a.hi&~b.hi};}
Set site(int x){return x<64?Set{uint64_t(1)<<x,0}:Set{0,uint64_t(1)<<(x-64)};}
bool empty(Set a){return !(a.lo|a.hi);}
int count(Set a){return popcount(a.lo)+popcount(a.hi);}
int take(Set& a){if(a.lo){int v=countr_zero(a.lo);a.lo&=a.lo-1;return v;}
    int v=countr_zero(a.hi);a.hi&=a.hi-1;return v+64;}
Set full{~uint64_t(0),~uint64_t(0)};
int layer_limit=51;
array<Set,128> nearv;Set even;
constexpr array<uint64_t,6> lower={0x5555555555555555ull,0x3333333333333333ull,
    0x0f0f0f0f0f0f0f0full,0x00ff00ff00ff00ffull,0x0000ffff0000ffffull,0x00000000ffffffffull};
inline uint64_t within(uint64_t a){
    uint64_t out=0;
    for(int j=0;j<6;j++){int s=1<<j;out|=(a&lower[j])<<s | (a&~lower[j])>>s;}
    return out;
}
Set expand(Set a){return {within(a.lo)|a.hi,within(a.hi)|a.lo};}
int capacity(Set allowed,int root){
    Set seen=site(root),front=seen;
    while(!empty(front)){
        Set next=without(expand(front)&allowed,seen);seen=seen|next;front=next;
    }
    int e=count(seen&even),o=count(seen)-e;
    if(popcount(unsigned(root))%2)swap(e,o);
    return min(2*e,2*o+1);
}
struct Search{
    Set A{},B{};int target,minimum,other_root=-1,other_tip=-1;
    uint64_t visits=0,arms=0,calls=0,budget;
    bool capped=false;
    vector<int> C,D,ansC,ansD,hintC,hintD;
    template<class F>bool choices(Set choices,int depth,const vector<int>&hint,F continuation){
        if(depth<int(hint.size())){
            int x=hint[depth];if(!empty(choices&site(x))){
                choices=without(choices,site(x));if(continuation(x))return true;
            }
        }
        while(!empty(choices))if(continuation(take(choices)))return true;
        return false;
    }
    bool finish(int at,Set allowed,int need){
        if(++arms+visits>budget){capped=true;return true;}
        int n=int(D.size());
        if(n>=need){if(other_tip<0||at==other_tip){ansC=C;ansD=D;return true;}return false;}
        if(at==other_tip)return false;
        if(n+count(allowed)<need || n-1+capacity(allowed,at)<need)return false;
        Set next=without(allowed,nearv[at]);
        Set options=nearv[at]&allowed;
        if(other_tip>=0&&!empty(options&site(other_tip)))options=site(other_tip);
        return choices(options,n,hintD,[&](int v){
            D.push_back(v);bool stop=finish(v,next,need);D.pop_back();return stop;
        });
    }
    bool grow(int at,Set allowed,Set used){
        if(++visits+arms>budget){capped=true;return true;}
        int n=int(C.size());
        Set options=nearv[at]&allowed,next=without(allowed,nearv[at]);
        if(n<int(hintC.size()) && equal(C.begin(),C.end(),hintC.begin())){
            int v=hintC[n];
            if(!empty(options&site(v))){
                options=without(options,site(v));C.push_back(v);
                bool stop=grow(v,next,used|site(v));C.pop_back();if(stop)return true;
            }
        }
        if(n>=minimum && (other_root>=0 || empty(A&site(at)))){
            int need=target-n,root=other_root>=0?other_root:at;
            Set domain=without(full,A|used|site(root));
            bool correct_tip=other_tip<0 || (root!=other_tip && !empty(domain&site(other_tip)) &&
                    (popcount(unsigned(root^other_tip))%2)==(need-1)%2);
            if(need>=2 && need<=layer_limit && correct_tip && capacity(domain,root)>=need){
                ++calls;D={root};if(finish(root,domain,need))return true;
            }
        }
        if(n>=layer_limit || n+count(allowed)<minimum || n-1+capacity(allowed,at)<minimum)return false;
        return choices(options,n,hintC,[&](int v){
            C.push_back(v);bool stop=grow(v,next,used|site(v));C.pop_back();return stop;
        });
    }
};
int main(int argc,char**argv){
    if(argc>3 && string(argv[argc-1])=="q3"){full={255,0};layer_limit=5;--argc;}
    if(argc<3||argc>6)return 2;
    string mode=argc>3?argv[3]:"prefix";
    if(mode!="prefix"&&mode!="middle"&&mode!="outer")return 2;
    for(int x=0;x<128;x++){
        if(!(popcount(unsigned(x))%2))even=even|site(x);
        nearv[x]=expand(site(x))&full;
    }
    int index;while(cin>>index){
        array<vector<int>,4> paths;
        for(auto& q:paths){int n,v;cin>>n;for(int i=0;i<n;i++){cin>>v;q.push_back(v);}}
        Search s;int left=1,right=0,root=paths[1].back();
        s.hintC=paths[2];s.hintD=paths[3];
        if(mode=="middle"){
            left=1;right=2;root=paths[1].front();s.other_root=paths[2].back();
            s.hintC=paths[0];reverse(s.hintC.begin(),s.hintC.end());s.hintD=paths[3];
        }
        if(mode=="outer"){
            if(argc!=6)return 2;
            left=0;right=3;root=stoi(argv[4])?paths[0].front():paths[0].back();
            s.other_tip=stoi(argv[5])?paths[3].back():paths[3].front();
            s.hintC=paths[1];s.hintD=paths[2];
        }
        s.target=stoi(argv[1])-int(paths[left].size()+paths[right].size());
        s.budget=stoull(argv[2]);s.minimum=max(2,s.target-layer_limit);
        for(int v:paths[right])s.A=s.A|site(v);
        for(int v:paths[left])s.B=s.B|site(v);
        if(s.other_root>=0)s.B=s.B|site(s.other_root);
        if(s.other_tip>=0){s.B=s.B|site(s.other_tip);s.A=without(s.A,site(s.other_tip));}
        s.C={root};s.grow(root,without(full,s.B),site(root));
        cout<<index<<" "<<(!s.ansC.empty()?"FOUND":s.capped?"OPEN":"EXHAUSTED")<<" "<<s.visits<<" "<<s.arms<<" "<<s.calls;
        for(const auto& q:{s.ansC,s.ansD}){cout<<" "<<q.size();for(int x:q)cout<<" "<<x;}
        cout<<endl;
    }
}
