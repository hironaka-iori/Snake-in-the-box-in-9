#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
string normalized(string s){
    array<int,9> m; m.fill(-1);int next=0;
    for(char& c:s){int d=c-'0';if(d<0||d>8)throw runtime_error("axis");if(m[d]<0)m[d]=next++;c=char('0'+m[d]);}
    return s;
}
string canonical(string s){
    string a=normalized(s); reverse(s.begin(),s.end()); return min(a,normalized(s));
}
struct Search {
    array<int,512> near{},used{};
    vector<int> left,right,core;
    int goal,dimensions=9;
    uint64_t nodes=0;
    void mark(int x,int s){used[x]+=s;for(int d=0;d<dimensions;d++)near[x^(1<<d)]+=s;}
    bool dfs(int a,int b,bool leftOpen,int n){
        ++nodes;
        if(n>=goal+1){
            vector<int> v(left.rbegin(),left.rend());
            v.insert(v.end(),core.begin(),core.end());v.insert(v.end(),right.begin(),right.end());
            for(int j=0;j<int(v.size());j++)for(int i=0;i<j;i++){
                int dist=popcount(unsigned(v[i]^v[j]));if(!dist||((dist==1)!=(i+1==j)))throw runtime_error("invalid witness");
            }
            cout<<"FOUND "<<v.size()-1;for(int x:v)cout<<" "<<x;cout<<endl;return true;
        }
        if(leftOpen&&dfs(a,b,false,n))return true;
        int tip=leftOpen?a:b;auto& side=leftOpen?left:right;
        for(int d=0;d<dimensions;d++){
            int x=tip^(1<<d);if(used[x]||near[x]!=1)continue;
            mark(x,1);side.push_back(x);
            if(dfs(leftOpen?x:a,leftOpen?b:x,leftOpen,n+1))return true;
            side.pop_back();mark(x,-1);
        }
        return false;
    }
    bool run(const string&w,int target){
        goal=target;core={0};mark(0,1);int x=0;
        for(char c:w){x^=1<<(c-'0');if(used[x]||near[x]!=1)throw runtime_error("not induced");core.push_back(x);mark(x,1);}
        bool found=dfs(core.front(),core.back(),true,int(core.size()));
        for(int y:core)mark(y,-1);return found;
    }
};
#ifndef Q9_TIP_LIBRARY
int main(int argc,char**argv){
    if(argc<4)return 2;
    int goal=stoi(argv[1]),trim=stoi(argv[2]);set<string> roots,parents; 
    for(int i=3;i<argc;i++){
        ifstream input(argv[i]);if(!input)throw runtime_error("file");string w;
        while(input>>w){if(w.size()<=trim+1)throw runtime_error("short input");parents.insert(canonical(w));}
    }
    for(const string&w:parents)for(int l=0;l<=trim;l++)roots.insert(canonical(w.substr(l,w.size()-trim)));
    set<string> visited=roots;
    const char* flipCount=std::getenv("Q9_CORE_FLIP");
    int depth=flipCount?stoi(flipCount):0;
    for(int round=0;!roots.empty()&&(depth<0||round<depth);round++){
        set<string> flipped;
        for(const string& r:roots){
            vector<int> path{0};array<int,512> adj{},present{};
            for(char c:r)path.push_back(path.back()^(1<<(c-48)));
            for(int v:path){present[v]=1;for(int d=0;d<9;d++)adj[v^(1<<d)]++;}
            for(int j=1;j+1<int(path.size());j++){
                int v=path[j-1]^path[j]^path[j+1];
                if(present[v]||adj[v]!=2)continue;
                string t=r;swap(t[j-1],t[j]);t=canonical(t);
                if(visited.insert(t).second)flipped.insert(t);
            }
        }
        cout<<"SQUARE "<<roots.size()<<" "<<flipped.size()<<endl;
        roots.swap(flipped);
    }
    if(depth<0)roots.swap(visited);
    cout<<"START "<<goal<<" "<<trim<<" "<<parents.size()<<" "<<roots.size()<<endl;
    Search s;int checked=0;
    for(const string& r:roots){if(s.run(r,goal))return 0;if(++checked%10000==0)cout<<"AT "<<checked<<" "<<s.nodes<<endl;}
    cout<<"DONE "<<checked<<" "<<s.nodes<<endl;
}
#endif
