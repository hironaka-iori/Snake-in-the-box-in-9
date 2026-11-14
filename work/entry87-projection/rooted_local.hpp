#pragma once
#include <array>
struct RootedLocal {
    std::array<bool,256> in{};
    std::array<int,256> n{},address{},deg{},tip{};
    std::array<std::array<unsigned char,256>,256> multiplicity{};
    int isolated=0,leaves=0,unmarked=0;
    void tally(int x,int s){
        if(!in[x])return;
        isolated+=s*(deg[x]==0);
        if(x && deg[x]==1){leaves+=s;if(tip[x]==0)unmarked+=s;}
    }
    void count(int w,int s){
        if(n[w]==1){int x=address[w];tally(x,-1);tip[x]+=s;tally(x,1);return;}
        if(n[w]!=2)return;
        int x=-1;
        for(int b=0;b<8;++b){int v=w^(1<<b);if(in[v]){x=v;break;}}
        int y=address[w]^x;
        int before=multiplicity[x][y],after=before+s;
        multiplicity[x][y]=multiplicity[y][x]=after;
        if((before==0)==(after==0))return;
        tally(x,-1);tally(y,-1);deg[x]+=s;deg[y]+=s;tally(x,1);tally(y,1);
    }
    void toggle(int v){
        int sign=in[v]?-1:1;
        for(int b=0;b<8;++b)count(v^(1<<b),-1);
        tally(v,-1);in[v]=!in[v];tally(v,1);
        for(int b=0;b<8;++b){int w=v^(1<<b);n[w]+=sign;address[w]^=v;count(w,1);}
    }
};
