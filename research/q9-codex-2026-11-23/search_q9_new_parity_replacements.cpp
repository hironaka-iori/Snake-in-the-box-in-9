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
    if(argc!=3)return 2;int goal=stoi(argv[1]),omissions=stoi(argv[2]);
    // Each input has two fewer vertices of the target opposite-tip class when one is omitted.
    string word;int id=0;
    while(cin>>word){
        vector<int> path{0};for(char c:word)path.push_back(path.back()^(1<<(c-'0')));
        for(int j=0;j<path.size();j++)for(int k=0;k<j;k++)
            if(path[j]==path[k]||((popcount(unsigned(path[j]^path[k]))==1)!=(j==k+1)))return 3;
        for(int side=0;side<2;side++){
            vector<int> src,free;
            for(int i=side;i<path.size();i+=2)src.push_back(path[i]);
            int n=src.size();if(2*(n+1)!=goal) return 4;
            Bounds state;for(int x:src)state.change(x,1);
            for(int x=0;x<512;x++)if(!state.occupied[x]&&__builtin_parity(unsigned(x^src.front()))==0)free.push_back(x);
            uint64_t eligible=0,total=0,pruned=0,unknown=0;
            for(int omit=omissions?0:-1;omit<(omissions?n:0);omit++){
                if(omit>=0)state.change(src[omit],-1);
                vector<int> choices;
                for(int x:free){
                    state.change(x,1);
                    if(!state.poor)choices.push_back(x);
                    state.change(x,-1);
                }
                total+=omit<0?free.size():free.size()*(free.size()-1)/2;
                for(int i=0;i<choices.size();i++){
                    int x=choices[i];state.change(x,1);
                    for(int j=omit<0?-1:i+1;j<(omit<0?0:int(choices.size()));j++){
                        if(j>=0)state.change(choices[j],1);
                        if(!state.poor && state.counts[1]>=2 && state.counts[2]>=n){
                            vector<int> chosen;for(int v=0;v<512;v++)if(state.occupied[v])chosen.push_back(v);
                            if(chosen.size()!=n+1)abort();
                            eligible++;Search s(chosen,100000,false);
                            if(s.test())return 0;unknown+=s.unknown;
                        }
                        if(j>=0)state.change(choices[j],-1);
                    }
                    state.change(x,-1);
                }
                if(omit>=0)state.change(src[omit],1);
            }
            cout<<"ROW "<<id<<" "<<side<<" "<<total<<" "<<eligible<<" "<<unknown<<endl;
        }id++;
    }
}
