// Generate DIMACS for a walk where each step can choose either of two axes.
// Compress all interval-distance constraints using component parities.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
using V=vector<int>;
struct CNF {
    int n=0;vector<V> cls;map<pair<int,int>,int> diff;
    int var(){return ++n;}
    void eqxor(int x,int a,int b,bool flip=false){
        if(flip)x=-x;cls.push_back({-x,a,b});cls.push_back({-x,-a,-b});cls.push_back({x,a,-b});cls.push_back({x,-a,b});
    }
    int differs(int a,int b){if(a==b)return 0;if(a>b)swap(a,b);
        auto [it,ok]=diff.emplace(make_pair(a,b),0);if(ok){it->second=var();eqxor(it->second,a,b);}return it->second;
    }
};
int main(int argc,char**argv){
    if(argc!=3)return 2;string wa=argv[1],wb=argv[2];if(wa.size()!=wb.size())return 2;
    vector<array<int,9>> states(1);CNF f;V selectors;int n=wa.size();
    for(int& x:states[0]){x=f.var();f.cls.push_back({-x});}
    for(int t=0;t<n;t++){
        int a=wa[t]-'0',b=wb[t]-'0';auto pos=states.back();int sel=f.var();selectors.push_back(sel);
        if(a==b){
            f.cls.push_back({sel});int x=f.var();f.cls.push_back({x,pos[a]});f.cls.push_back({-x,-pos[a]});pos[a]=x;
        }else for(int d:{a,b}){int x=f.var();f.eqxor(x,pos[d],sel,d==b);pos[d]=x;}
        states.push_back(pos);
    }
    set<V> clauses;int impossible=0;
    for(int i=0;i<n;i++){
        array<int,9> group{};for(int d=0;d<9;d++)group[d]=1<<d;
        int disp=0;
        for(int j=i+1;j<=n;j++){
            int a=wa[j-1]-'0',b=wb[j-1]-'0';disp^=1<<a;
            if(group[a]!=group[b]){
                int mask=group[a]|group[b];for(int bits=mask;bits;bits&=bits-1)group[countr_zero(unsigned(bits))]=mask;
            }
            if(j-i<=1)continue;
            int odd=0,howmany=0;
            for(int d=0;d<9;d++)if(countr_zero(unsigned(group[d]))==unsigned(d) && (popcount(unsigned(group[d]&disp))&1)){odd=group[d];howmany++;}
            if(howmany>=2)continue;
            V outside,inside;
            for(int d=0;d<9;d++)if(countr_zero(unsigned(group[d]))!=unsigned(d)){
                int z=f.differs(states[i][d],states[j][d]);if(z)(odd&(1<<d)?inside:outside).push_back(z);
            }
            if(inside.size()<2){sort(outside.begin(),outside.end());clauses.insert(outside);if(outside.empty())impossible++;}
            else for(int except:inside){V q=outside;for(int x:inside)if(x!=except)q.push_back(x);sort(q.begin(),q.end());clauses.insert(q);}
        }
    }
    cout<<"c selectors";for(int x:selectors)cout<<" "<<x;cout<<"\n";
    if(impossible){cout<<"p cnf "<<f.n<<" 1\n0\n";return 0;}
    cout<<"p cnf "<<f.n<<" "<<f.cls.size()+clauses.size()<<"\n";
    for(auto& q:f.cls){for(int x:q)cout<<x<<" ";cout<<"0\n";}
    for(auto& q:clauses){for(int x:q)cout<<x<<" ";cout<<"0\n";}
}
