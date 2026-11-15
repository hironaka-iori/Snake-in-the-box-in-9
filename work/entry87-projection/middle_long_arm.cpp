// Place a catalogued long outer arm and grow the complete other arm at the second crossing.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
struct Node {std::array<int,8> child{};};
int main(){
    int nm,nw,minimum,short_cap,target;
    if(!(std::cin>>nm>>nw>>minimum>>short_cap>>target))return 2;
    std::vector<std::vector<int>> middles(nm);
    for(auto& q:middles){int n;std::cin>>n;q.resize(n);for(auto& v:q)std::cin>>v;}
    std::vector<Node> trie(1);
    for(int i=0;i<nw;++i){
        std::string w;std::cin>>w;int nd=0;
        for(char c:w){int j=c-'0',next=trie[nd].child[j];
            if(!next){next=trie.size();trie[nd].child[j]=next;trie.emplace_back();}
            nd=next;
        }
    }
    std::cerr<<"trie "<<trie.size()<<" "<<nw<<std::endl;
    for(int index=0;index<nm;++index){
        auto m=middles[index];std::uint64_t states=0,placements=0,short_states=0;
        for(int side=0;side<2;++side){
            if(side)std::reverse(m.begin(),m.end());
            std::array<bool,256> blocked{};std::array<int,256> banned{};
            for(int v:m){blocked[v]=true;if(v!=m.back())++banned[v];}
            for(int j=0;j<8;++j)blocked[m.back()^(1<<j)]=true;
            std::vector<int> longer{m.front()},shorter;std::array<int,8> image{};
            auto closed=[&](int v,int change){banned[v]+=change;for(int b=0;b<8;++b)banned[v^(1<<b)]+=change;};
            closed(m.front(),1);
            auto capacity=[&](int start){
                std::array<bool,256> seen{};std::array<int,256> queue{};
                int head=0,tail=1,same=0;queue[0]=start;seen[start]=true;
                while(head<tail){
                    int v=queue[head++];same+=(std::popcount(unsigned(v^start))%2==0);
                    for(int b=0;b<8;++b){int w=v^(1<<b);if(seen[w]||banned[w])continue;
                        seen[w]=true;queue[tail++]=w;}
                }
                return std::min(2*same,2*(tail-same)+1);
            };
            auto short_path=[&](auto&& self,int v,int left)->bool{
                ++short_states;if(!left)return true;
                if(left>10&&(shorter.size()==1||shorter.size()%4==0)&&capacity(v)<left+1)return false;
                for(int b=0;b<8;++b){int w=v^(1<<b);if(banned[w])continue;
                    closed(v,1);shorter.push_back(w);
                    if(self(self,w,left-1))return true;
                    shorter.pop_back();closed(v,-1);
                }
                return false;
            };
            auto place=[&](auto&& self,int n,int v,int named,int used)->bool{
                ++states;int size=longer.size();int needed=target-int(m.size())-size;
                if(needed<1)return false;
                if(size>=minimum&&needed<=short_cap){
                    ++placements;shorter={m.back()};
                    if(!banned[m.back()]&&short_path(short_path,m.back(),needed-1))return true;
                }
                if(needed==1)return false;
                for(int label=0;label<=named&&label<8;++label){
                    int nd=trie[n].child[label];if(!nd)continue;
                    for(int j=0;j<8;++j){
                        if(label<named?image[label]!=j:bool(used&(1<<j)))continue;
                        int w=v^(1<<j);if(blocked[w])continue;
                        if(label==named)image[label]=j;
                        longer.push_back(w);closed(w,1);
                        if(self(self,nd,w,named+(label==named),used|(1<<j)))return true;
                        closed(w,-1);longer.pop_back();
                    }
                }
                return false;
            };
            if(place(place,0,m.front(),0,0)){
                std::cout<<"found "<<index<<' '<<side<<' '<<longer.size();
                for(int v:longer)std::cout<<' '<<v;
                std::cout<<' '<<shorter.size();for(int v:shorter)std::cout<<' '<<v;
                std::cout<<std::endl;return 0;
            }
        }
        std::cout<<"done "<<index<<' '<<states<<' '<<placements<<' '<<short_states<<std::endl;
    }
}
