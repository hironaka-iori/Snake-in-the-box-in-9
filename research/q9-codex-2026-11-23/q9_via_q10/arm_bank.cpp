// Enumerate all projected words at a fixed length, modulo cube isometry and with
// the seam-to-tip orientation preserved. Stop a partial map at its first chord.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
string canon(string w){array<int,16> m;m.fill(-1);int cnt=0;for(char& z:w){int k=z-'A';if(m[k]<0)m[k]=cnt++;z='A'+m[k];}return w;}
struct Project{
    const string& w;set<string>& out;int dim;array<int,16> map;array<int,512> shadow{};array<bool,512> used{};
    uint64_t nodes=0;string word;
    Project(const string& s,set<string>& bank,int d):w(s),out(bank),dim(d){map.fill(-1);update(0,1);}
    void update(int v,int a){used[v]=a>0;shadow[v]+=a;for(int b=1;b<512;b*=2)shadow[v^b]+=a;}
    void dfs(int i,int x,int opened,int colors){
        if(colors+dim-opened<9)return;++nodes;
        if(i==int(w.size())){out.insert(word);return;}
        int d=w[i]-'A',fixed=map[d],lo=fixed<0?0:fixed,hi=fixed<0?min(colors+1,9):fixed+1;
        for(int a=lo;a<hi;a++){
            int y=x^(1<<a);if(used[y]||shadow[y]!=1)continue;
            map[d]=a;update(y,1);word.push_back('A'+a);
            dfs(i+1,y,opened+(fixed<0),max(a+1,colors));
            word.pop_back();update(y,-1);map[d]=fixed;
        }
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;int dim=stoi(argv[1]),len=stoi(argv[2]);ifstream in(argv[3]);ofstream dst(argv[4]);
    string line;unordered_set<string> seen;set<string> bank;uint64_t work=0,rows=0;
    while(getline(in,line)){
        istringstream s(line);int d,x,prev;s>>d;if(d!=dim)continue;s>>prev;string w;
        while(s>>x){w.push_back('A'+countr_zero(unsigned(prev^x)));prev=x;}
        for(int k=0;k+len<=int(w.size());k++){
            string a=canon(w.substr(k,len)),b=a;reverse(b.begin(),b.end());b=canon(b);a=min(a,b);
            if(seen.insert(a).second){Project p(a,bank,dim);p.dfs(0,0,0,0);work+=p.nodes;}
        }cout<<"ROW "<<rows++<<" "<<seen.size()<<" "<<bank.size()<<" "<<work<<endl;
    }
    set<string> doubled=bank;for(auto w:bank){reverse(w.begin(),w.end());doubled.insert(canon(w));}
    for(auto& w:doubled)dst<<w<<'\n';
    cout<<"DONE "<<rows<<" "<<seen.size()<<" "<<doubled.size()<<" "<<work<<endl;
}
