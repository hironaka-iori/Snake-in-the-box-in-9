// Put four independently oriented Q7 paths in Q2 Gray order. Equal inner
// addresses of neighbouring layers are exactly their cross-layer adjacencies.
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Node {array<int,7> child{};bool end=false;};
using Set=array<bool,128>;
array<vector<Node>,4> trees;
array<vector<string>,4> words;
array<vector<int>,4> placed;
uint64_t nodes=0,placements=0,limit;
bool found=false,cutoff=false;

bool layer(int index) {
    if(index==4) {found=true;return true;}
    const auto& previous=placed[index-1];int anchor=previous.back();
    Set forbidden{};
    for(int v:previous)forbidden[v]=true;
    if(index==3)for(int v:placed[0])forbidden[v]=true;
    if(index==3)for(int v:placed[0])if(v==anchor)return false;
    array<int,7> mapping{};
    placed[index]={anchor};
    auto search=[&](auto&& self,int node,int at,int named,int use)->bool {
        if(++nodes>limit){cutoff=true;return true;}
        if(trees[index][node].end) {++placements;if(layer(index+1))return true;}
        for(int b=0;b<=named && b<7;++b) {
            int child=trees[index][node].child[b];if(!child)continue;
            for(int axis=0;axis<7;++axis) {
                if(b<named ? axis!=mapping[b] : (use&(1<<axis))!=0)continue;
                int v=at^(1<<axis);if(forbidden[v])continue;
                if(b==named)mapping[b]=axis;
                placed[index].push_back(v);
                if(self(self,child,v,named+(b==named),use|(1<<axis)))return true;
                placed[index].pop_back();
            }
        }
        return false;
    };
    return search(search,0,anchor,0,0);
}
int main(int argc,char**argv) {
    if(argc!=2)return 2;limit=strtoull(argv[1],nullptr,10);
    for(int i=0;i<4;++i) {
        int n;if(!(cin>>n))return 3;
        trees[i].emplace_back();
        for(int j=0;j<n;++j) {
            string word;cin>>word;words[i].push_back(word);int p=0;
            for(char c:word){
                int b=c-'0';if(b<0||b>=7)return 4;
                if(!trees[i][p].child[b]){
                    trees[i][p].child[b]=int(trees[i].size());trees[i].emplace_back();
                }
                p=trees[i][p].child[b];
            }
            trees[i][p].end=true;
        }
    }
    for(const auto& word:words[0]) {
        int v=0;placed[0]={0};
        for(char c:word){v^=1<<(c-'0');placed[0].push_back(v);}
        if(layer(1))break;
    }
    cout<<(found?"FOUND":cutoff?"OPEN":"EXHAUSTED")<<" "<<placements<<" "<<nodes;
    if(found){
        array<int,4> gray={0,1,3,2};
        for(int i=0;i<4;++i)for(int v:placed[i])cout<<" "<<(v|(gray[i]<<7));
    }
    cout<<"\n";
}
