#pragma once
#include <array>
#include <cstdint>
#include <vector>

struct Board {
    int d, n, size=0, bad=0, tips=0;
    std::array<int,512> used{},degree{};
    std::array<std::uint64_t,8> bad_sites{};
    std::array<std::array<int,10>,512> ball{};
    explicit Board(int dimension):d(dimension),n(1<<d) {
        for(int v=0;v<n;v++){
            ball[v][0]=v;
            for(int j=0;j<d;j++) ball[v][j+1]=v^(1<<j);
        }
    }
    void account(int v,int sign) {
        if(!used[v]) return;
        if(degree[v]==0||degree[v]>2) {
            bad+=sign;
            bad_sites[v>>6]^=std::uint64_t(1)<<(v&63);
        }
        tips+=sign*(degree[v]==1);
    }
    void toggle(int v) {
        const int delta=used[v]?-1:1;
        account(v,-1); used[v]^=1; size+=delta; account(v,1);
        for(int j=1;j<=d;j++){
            int y=ball[v][j]; account(y,-1); degree[y]+=delta; account(y,1);
        }
    }
    void star(int v) { for(int j=0;j<=d;j++) toggle(ball[v][j]); }
    std::vector<int> path() const {
        int start=0;
        while(start<n&&(!used[start]||degree[start]!=1)) ++start;
        std::vector<int> out;
        int previous=-1,at=start;
        while(at<n){
            out.push_back(at); int next=n;
            for(int j=1;j<=d;j++){
                int y=ball[at][j]; if(y!=previous&&used[y]) next=y;
            }
            previous=at; at=next;
        }
        if(int(out.size())!=size) out.clear();
        return out;
    }
};
