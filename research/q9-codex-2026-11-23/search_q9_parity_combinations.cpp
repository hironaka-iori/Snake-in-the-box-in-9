#include <cassert>
// Fix one parity class only. All opposite-parity vertices and their order are free.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <sstream>
struct Bounds{
    array<unsigned char,512> occupied{},load{};
    array<int,512> room{};
    int poor=0,counts[10]{};
    Bounds(){room.fill(9);}
    void change(int x,int sign){
        if(sign<0){poor-=room[x]<2;occupied[x]=false;}
        for(int d=0;d<9;d++){
            int odd=x^(1<<d),prev=load[odd],after=prev+sign;load[odd]=after;
            if(prev)counts[prev]--;if(after)counts[after]++;
            if((prev<=2)==(after<=2))continue;
            int delta=after<=2?1:-1;
            for(int k=0;k<9;k++){int v=odd^(1<<k);int before=room[v];room[v]+=delta;
                if(occupied[v])poor+=(room[v]<2)-(before<2);}
        }
        if(sign>0){occupied[x]=true;poor+=room[x]<2;}
    }
};
int main(int argc,char**argv){
    if(argc!=5 && argc!=6)return 2; bool sets=(argc==6 && string(argv[5])=="sets");
    int goal=stoi(argv[1]),drops=stoi(argv[2]),offset=stoi(argv[3]),stride=stoi(argv[4]);
    if(drops<0||drops>4||offset<0||offset>=stride)return 2;
    string word;int id=-1;
    while(getline(cin,word)){
        ++id;if(id%stride!=offset)continue;vector<int> path{0};
        if(!sets)for(char c:word)path.push_back(path.back()^(1<<(c-'0')));
        for(int j=0;j<path.size();j++)for(int k=0;k<j;k++)
            if(path[j]==path[k]||((popcount(unsigned(path[j]^path[k]))==1)!=(j==k+1)))return 3;
        for(int side=0;side<(sets?1:2);side++){
            vector<int> src,free;
            if(sets){istringstream ss(word);int v;while(ss>>v)src.push_back(v);}
            else for(int i=side;i<path.size();i+=2)src.push_back(path[i]);
            int n=src.size(),gain=goal/2-n;if(!n||gain<0||gain>1)return 4;
            array<bool,512> check{};for(int v:src){if(v<0||v>=512||check[v]||__builtin_parity(unsigned(v^src.front())))return 4;check[v]=true;}
            Bounds state;for(int x:src)state.change(x,1);
            for(int x=0;x<512;x++)if(!state.occupied[x]&&__builtin_parity(unsigned(x^src.front()))==0)free.push_back(x);
            uint64_t tested=0,branches=0,removals=0,unknown=0;
            auto add=[&](auto&&self,const vector<int>& candidates,int start,int needed)->bool{
                if(needed==0){
                    if(state.poor||state.counts[1]<2||state.counts[2]<goal/2-1)return false;
                    vector<int> chosen;for(int v=0;v<512;v++)if(state.occupied[v])chosen.push_back(v);
                    assert(chosen.size()==goal/2);tested++;Search s(chosen,100000,false);
                    if(s.test())return true;unknown+=s.unknown;return false;
                }
                for(int j=start;j+needed<=candidates.size();j++){
                    int x=candidates[j];state.change(x,1);branches++;
                    if(!state.poor && self(self,candidates,j+1,needed-1))return true;
                    state.change(x,-1);
                }return false;
            };
            auto remove=[&](auto&&self,int start,int todo)->bool{
                if(todo==0){
                    removals++;
                    if(state.poor)return false;
                    vector<int> choices;
                    for(int v:free){state.change(v,1);if(!state.poor)choices.push_back(v);state.change(v,-1);}
                    return add(add,choices,0,drops+gain);
                }
                for(int j=start;j+todo<=n;j++){
                    state.change(src[j],-1);
                    if(self(self,j+1,todo-1))return true;
                    state.change(src[j],1);
                }return false;
            };
            if(remove(remove,0,drops))return 0;
            cout<<"ROW "<<id<<" "<<side<<" "<<removals<<" "<<branches<<" "<<tested<<" "<<unknown<<endl;
        }
    }
    return 0;
}

