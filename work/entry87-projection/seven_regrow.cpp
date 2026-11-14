// Close a bank of equal-length Q7 paths under regrowth of a full endpoint arm.
#include <algorithm>
#include <array>
#include <cstdint>
#include <deque>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
struct Mask{array<uint64_t,4> data{};};
void mark(Mask&m,int v){m.data[v>>6]|=uint64_t(1)<<(v&63);}
bool has(const Mask&m,int v){return (m.data[v>>6]>>(v&63))&1;}
Mask merge(Mask a,const Mask& b){for(int i=0;i<4;i++)a.data[i]|=b.data[i];return a;}
Mask hood[256];
string normalize(const string&s){
    array<int,8> name{};name.fill(-1);int next=0;string out=s;
    for(char& c:out){int b=c-'0';if(name[b]<0)name[b]=next++;c=char('0'+name[b]);}
    return out;
}
string reversed(string s){reverse(s.begin(),s.end());return s;}
string canon(const string&s){return min(normalize(s),normalize(reversed(s)));}
int main(int argc,char**argv){
    if(argc!=5&&argc!=6)return 2;int size=stoi(argv[1]),trim=stoi(argv[2]),limit=stoi(argv[3]);
    int d=argc==6?stoi(argv[5]):7;if(d!=7&&d!=8)return 2;
    uint64_t maxnodes=stoull(argv[4]),nodes=0;bool cutoff=false;
    for(int v=0;v<(1<<d);++v){mark(hood[v],v);for(int b=0;b<d;++b)mark(hood[v],v^(1<<b));}
    unordered_set<string> paths,roots;deque<string> todo;
    auto keep=[&](const string&s){auto k=canon(s);if(paths.insert(k).second)todo.push_back(k);};
    for(string s;cin>>s;)if(int(s.size())==size-1)keep(s);
    int initial=int(paths.size());
    while(!todo.empty()&&!cutoff){
        string current=todo.front();todo.pop_front();
        for(const string& start:{current,reversed(current)}){
            string root=normalize(start.substr(0,size-1-trim));
            if(!roots.insert(root).second)continue;
            int v=0;Mask blocked{};
            for(char c:root){blocked=merge(blocked,hood[v]);v^=1<<(c-'0');}
            string word=root;
            auto grow=[&](auto&& self,int at,Mask fixed,int remaining)->void{
                if(++nodes>maxnodes||int(paths.size())>=limit){cutoff=true;return;}
                if(!remaining){keep(word);return;}
                Mask next=merge(fixed,hood[at]);
                for(int b=0;b<d&&!cutoff;++b){
                    int w=at^(1<<b);if(has(fixed,w))continue;
                    word.push_back(char('0'+b));self(self,w,next,remaining-1);word.pop_back();
                }
            };
            grow(grow,v,blocked,trim);if(cutoff)break;
        }
    }
    cout<<(cutoff?"OPEN":"CLOSED")<<" "<<initial<<" "<<paths.size()<<" "<<roots.size()<<" "<<nodes<<"\n";
    vector<string> sorted(paths.begin(),paths.end());sort(sorted.begin(),sorted.end());
    for(const string&s:sorted)cout<<s<<"\n";
}
