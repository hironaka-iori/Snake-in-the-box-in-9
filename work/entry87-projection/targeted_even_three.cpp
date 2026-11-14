// Exhaust three even substitutions on a designated face, if one newly used
// anchor is adjacent to the advertised collided odd address.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <set>
#include <vector>
#include "rooted_local.hpp"
using namespace std;

int main(int argc,char**argv){
    if(argc!=4)return 2;
    int cap=stoi(argv[1]),side=stoi(argv[2]),w=stoi(argv[3]);
    array<vector<int>,2> orig;
    set<int> used;
    for(int s=0;s<2;++s){int n;cin>>n;for(int i=0,v;i<n;++i){cin>>v;orig[s].push_back(v);used.insert(v);}}
    RootedLocal g;vector<int> remove,add,priority;
    for(int v:orig[side]){g.toggle(v);if(v)remove.push_back(v);}
    for(int v=0;v<256;++v)if(popcount(unsigned(v))%2==0 && !used.count(v)){
        add.push_back(v);
        if(popcount(unsigned(v^w))==1)priority.push_back(v);
    }
    uint64_t cases=0,passing=0;
    for(int a:priority){g.toggle(a);
        for(int b:add){
            if(b==a || (popcount(unsigned(b^w))==1 && b<a))continue;
            g.toggle(b);
            for(int c:add){
                if(c<=b || c==a || (popcount(unsigned(c^w))==1 && c<a))continue;
                g.toggle(c);
                for(int i=0;i<int(remove.size());++i){int x=remove[i];g.toggle(x);
                    for(int j=i+1;j<int(remove.size());++j){int y=remove[j];g.toggle(y);
                        for(int k=j+1;k<int(remove.size());++k){
                            int z=remove[k];g.toggle(z);++cases;
                            if(g.isolated==0 && g.leaves<=1 && (cap!=side || !g.unmarked)){
                                cout<<x<<' '<<y<<' '<<z<<' '<<a<<' '<<b<<' '<<c<<'\n';++passing;
                            }
                            g.toggle(z);
                        }g.toggle(y);
                    }g.toggle(x);
                }g.toggle(c);
            }g.toggle(b);
        }g.toggle(a);
    }
    cout<<"count "<<cases<<' '<<passing<<' '<<priority.size()<<'\n';
}
