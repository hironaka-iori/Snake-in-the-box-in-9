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

int main(int argc,char**argv) {
    const int bridge=argc>1?stoi(argv[1]):0;
    const bool opposite_faces=argc>2 && string(argv[2])=="opposite-faces";
    if(opposite_faces && bridge!=0)return 2;
    const bool census=opposite_faces && argc>=4;
    const int max_contacts=census?stoi(argv[3]):0;
    if(max_contacts<0 || max_contacts>8)return 2;
    array<uint64_t,9> contacts{};
    const uint64_t save_limit=argc==5?stoull(argv[4]):0;
    const int dimension=opposite_faces?8:9;
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
            if(!opposite_faces)for(int b=0;b<9;++b) blocked[v^(1<<b)]=true;
        }
        array<int,9> image{};
        vector<int> bridge_steps;
        auto visit=[&](auto&& self,int p,int at,int named,int used,int hits)->bool {
            ++states;
            if(nodes[p].leaf>=0) {
                ++leaves;
                if(census){
                    ++contacts[hits];
                    if(contacts[hits]<=save_limit){
                        cout<<"sample "<<hits<<" "<<l<<" "<<nodes[p].leaf;
                        for(int i=0;i<named;++i)cout<<" "<<image[i];
                        cout<<"\n";
                    }
                    return false;
                }
                cout<<"found "<<l<<" "<<nodes[p].leaf<<" "<<named;
                for(int i=0;i<named;++i) cout<<" "<<image[i];
                cout<<" "<<states<<" "<<bridge_steps.size();
                for(int b:bridge_steps) cout<<" "<<b;
                cout<<"\n"; return true;
            }
            for(int b=0;b<=named && b<dimension;++b) {
                int child=nodes[p].child[b]; if(!child) continue;
                if(b<named) {
                    int next=at^(1<<image[b]);
                    int count=hits+blocked[next];
                    if(count<=max_contacts && self(self,child,next,named,used,count)) return true;
                } else {
                    for(int axis=0;axis<dimension;++axis) {
                        if(used&(1<<axis)) continue;
                        int next=at^(1<<axis),count=hits+blocked[next]; if(count>max_contacts) continue;
                        image[b]=axis;
                        if(self(self,child,next,named+1,used|(1<<axis),count)) return true;
                    }
                }
            }
            return false;
        };
        // Vertex zero is the active hinge. 'blocked' is the union of the
        // closed neighbourhoods of all preceding non-hinge vertices.
        auto grow=[&](auto&& self,int at,int remaining)->bool {
            if(!remaining) return visit(visit,0,at,0,0,0);
            for(int b=0;b<9;++b) {
                int next=at^(1<<b);
                if(blocked[next]) continue;
                array<int,10> fresh{}; int count=0;
                auto mark=[&](int x){if(!blocked[x]) {blocked[x]=true;fresh[count++]=x;}};
                mark(at); for(int a=0;a<9;++a) mark(at^(1<<a));
                bridge_steps.push_back(b);
                if(self(self,next,remaining-1)) return true;
                bridge_steps.pop_back();
                for(int i=0;i<count;++i) blocked[fresh[i]]=false;
            }
            return false;
        };
        if(grow(grow,0,bridge)) return 0;
    }
    cout<<"complete "<<states<<" "<<leaves<<" "<<nodes.size()<<"\n";
    if(census){
        cout<<"counts";for(int i=0;i<=max_contacts;i++)cout<<" "<<contacts[i];cout<<"\n";
    }
}
