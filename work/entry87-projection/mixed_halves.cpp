// Join independently oriented rooted cube paths. A transition trie shares
// each common initial word of the moving arms across all its descendants.
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;

struct Node {
    array<int,9> child{};
    int leaf=-1;
};

int main() {
    int nl,nr;
    if (!(cin>>nl>>nr)) return 2;
    vector<string> left(nl),right(nr);
    for(auto& word:left) cin>>word;
    vector<Node> nodes(1);
    for(int r=0;r<nr;++r) {
        cin>>right[r]; int p=0;
        for(char c:right[r]) {
            int j=c-'0';
            if(!nodes[p].child[j]) {
                nodes[p].child[j]=int(nodes.size());
                nodes.emplace_back();
            }
            p=nodes[p].child[j];
        }
        nodes[p].leaf=r;
    }
    uint64_t states=0,leaves=0;
    for(int l=0;l<nl;++l) {
        array<bool,512> blocked{}; int v=0;
        for(char c:left[l]) {
            v^=1<<(c-'0'); blocked[v]=true;
            for(int b=0;b<9;++b) blocked[v^(1<<b)]=true;
        }
        array<int,9> image{};
        auto visit=[&](auto&& self,int p,int at,int named,int used)->bool {
            ++states;
            if(nodes[p].leaf>=0) {
                ++leaves; cout<<"found "<<l<<" "<<nodes[p].leaf<<" "<<named;
                for(int i=0;i<named;++i) cout<<" "<<image[i];
                cout<<" "<<states<<"\n"; return true;
            }
            for(int b=0;b<=named && b<9;++b) {
                int child=nodes[p].child[b]; if(!child) continue;
                if(b<named) {
                    int next=at^(1<<image[b]);
                    if(!blocked[next] && self(self,child,next,named,used)) return true;
                } else {
                    for(int axis=0;axis<9;++axis) {
                        if(used&(1<<axis)) continue;
                        int next=at^(1<<axis); if(blocked[next]) continue;
                        image[b]=axis;
                        if(self(self,child,next,named+1,used|(1<<axis))) return true;
                    }
                }
            }
            return false;
        };
        if(visit(visit,0,0,0,0)) return 0;
    }
    cout<<"complete "<<states<<" "<<leaves<<" "<<nodes.size()<<"\n";
}
