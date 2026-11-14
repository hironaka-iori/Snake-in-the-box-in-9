#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
#include "rooted_local.hpp"
using namespace std;
int main(int argc,char**argv){
    if(argc!=3)return 2;
    int edits=stoi(argv[1]),cap=stoi(argv[2]);if(edits!=1 && edits!=2)return 2;
    RootedLocal graph;vector<int> old,all,removed,added;
    for(int v;cin>>v;){graph.toggle(v);if(v)old.push_back(v);}
    for(int v=0;v<256;++v)if(popcount(unsigned(v))%2==0 && !graph.in[v])all.push_back(v);
    uint64_t count=0,passing=0;
    auto visit=[&](auto&& self,int at,int first)->void{
        if(at==2*edits){
            ++count;
            if(graph.isolated || graph.leaves>1 || (cap && graph.unmarked))return;
            ++passing;
            for(int v:removed)cout<<v<<' ';
            for(int v:added)cout<<v<<' ';
            cout<<'\n';return;
        }
        auto& inside=at<edits?old:all;
        auto& current=at<edits?removed:added;
        for(int i=first;i<int(inside.size());++i){
            int v=inside[i];graph.toggle(v);current.push_back(v);
            self(self,at+1,at+1==edits?0:i+1);
            current.pop_back();graph.toggle(v);
        }
    };
    visit(visit,0,0);cout<<"count "<<count<<' '<<passing<<'\n';
}
