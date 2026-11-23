// Join two Q8 paths embedded in independently oriented facets of Q9.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
string normalize(string s){
    array<int,8> lookup;lookup.fill(-1);int n=0;
    for(char& c:s){int i=c-'0';if(lookup[i]<0)lookup[i]=n++;c=char('0'+lookup[i]);}
    return s;
}
bool valid(const Path &p){
    for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){
        int d=popcount(unsigned(p[i]^p[j]));if(!d||(d==1)!=(j+1==i))return false;
    }
    return true;
}
Path vertices(string s){Path p{0};for(char c:s)p.push_back(p.back()^1<<(c-'0'));return p;}
struct Node{array<int,8> next{};int maxdepth=0;};
struct Solve{
    vector<Node> trie{Node{}}; Path a,b,answer;
    array<bool,512> forbidden{};array<int,8> image;int need,cutoff;
    uint64_t nodes=0,bridges=0,tested=0;
    int bridgeLen=1;
    Path connector;
    bool connect(){
        if(int(connector.size())==bridgeLen){
            need=cutoff-(int(a.size())-1)-bridgeLen;
            if(need<1||trie[0].maxdepth<need)return false;
            bridges++;image.fill(-1);b={connector.back()};return walk(0,0);
        }
        int tip=connector.empty()?0:connector.back();
        for(int d=0;d<9;d++){
            int x=tip^(1<<d);
            if(connector.empty()){
                bool hit=false;
                for(int v:a)if(v==x||(v!=0&&popcount(unsigned(v^x))==1)){hit=true;break;}
                if(hit)continue;
            }else if(forbidden[x])continue;
            array<bool,10> old{};old[0]=forbidden[x];forbidden[x]=true;
            for(int k=0;k<9;k++){int y=x^(1<<k);old[1+k]=forbidden[y];}
            // The current tip may have more neighbors in a continuation; forbid
            // its neighborhood only after choosing the next bridge vertex.
            array<bool,9> tipOld{};
            if(!connector.empty())for(int k=0;k<9;k++){int y=tip^(1<<k);tipOld[k]=forbidden[y];forbidden[y]=true;}
            connector.push_back(x);
            if(connect())return true;
            connector.pop_back();
            if(!connector.empty())for(int k=0;k<9;k++)forbidden[tip^(1<<k)]=tipOld[k];
            forbidden[x]=old[0];
        }
        return false;
    }
    void insert(const string& s){
        int n=0;trie[n].maxdepth=max(trie[n].maxdepth,(int)s.size());
        for(char c:s){
            int d=c-'0',q=trie[n].next[d];
            if(!q){q=trie.size();trie[n].next[d]=q;trie.push_back({});}
            n=q;trie[n].maxdepth=max(trie[n].maxdepth,(int)s.size());
        }
    }
    bool walk(int node,int used){
        nodes++;
        if(int(b.size())==need+1){
            answer.assign(a.rbegin(),a.rend());answer.insert(answer.end(),connector.begin(),connector.end()-1);answer.insert(answer.end(),b.begin(),b.end());
            if(!valid(answer)||int(answer.size())!=cutoff+1)abort();
            return true;
        }
        for(int i=0;i<8;i++)if(int u=trie[node].next[i];u && trie[u].maxdepth>=need){
            int free=image[i]<0?511^used:1<<image[i];
            while(free){
                int d=countr_zero(unsigned(free));free&=free-1;
                int x=b.back()^(1<<d);if(forbidden[x])continue;
                int prev=image[i];image[i]=d;b.push_back(x);
                if(walk(u,used|1<<d))return true;
                b.pop_back();image[i]=prev;
            }
        }
        return false;
    }
    bool run(const string& s){
        a=vertices(s);tested++;forbidden.fill(false);array<int,512> deg{};array<bool,512> in{};
        for(int v:a){in[v]=true;forbidden[v]=true;for(int j=0;j<9;j++){int w=v^(1<<j);deg[w]++;forbidden[w]=true;}}
        if(int(a.size())-1+bridgeLen+trie[0].maxdepth<cutoff)return false;
        return connect();

    }
};
int main(int argc,char **argv){
    if(argc<4)return 1;
    Solve solver;solver.cutoff=stoi(argv[1]);if(const char* v=getenv("Q9_BRIDGE_LENGTH"))solver.bridgeLen=stoi(v);if(solver.bridgeLen<1||solver.bridgeLen>6)return 2;int minimum=stoi(argv[2]);set<string> bank;
    for(int f=3;f<argc;f++){
        ifstream in(argv[f]);if(!in)return 2;string seq;
        while(in>>seq){
            for(char c:seq)if(c<'0'||c>'7')return 3;
            if(!valid(vertices(seq)))return 4;
            for(int i=0;i+minimum<=(int)seq.size();i++)for(int len=minimum;i+len<=(int)seq.size();len++){
                auto s=seq.substr(i,len);bank.insert(normalize(s));reverse(s.begin(),s.end());bank.insert(normalize(s));
            }
        }
    }
    for(auto &s:bank)solver.insert(s);
    vector<string> arms(bank.begin(),bank.end());
    stable_sort(arms.begin(),arms.end(),[](auto&a,auto&b){return a.size()>b.size();});
    for(auto &s:arms)if(solver.run(s)){
        cout<<"FOUND";for(int v:solver.answer)cout<<" "<<v;cout<<endl;return 0;
    }
    cout<<"NO_JOIN rooted "<<bank.size()<<" anchors "<<solver.tested<<" bridge_options "<<solver.bridges<<" partial_embeddings "<<solver.nodes<<endl;
}
