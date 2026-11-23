#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Trade {
    array<bool,512> used{}, changed{}, excluded{};
    array<int,512> degree{};
    set<int> bad;
    vector<int> path, edits;
    set<vector<int>> emitted;
    int s,t,budget,seed,nodes,limit;
    long long total=0,cutoffs=0;
    int want(int v) const { return v==s || v==t ? 1 : 2; }
    void check(int v) {
        bool invalid = used[v] ? degree[v]!=want(v) : (v==s || v==t);
        if(invalid) bad.insert(v); else bad.erase(v);
    }
    void flip(int v){
        used[v]=!used[v]; check(v);
        for(int d=0;d<9;d++){int n=v^(1<<d);degree[n]+=used[v]?1:-1;check(n);}
    }
    void setup(const vector<int>&p,int a,int b){
        path=p;s=a;t=b;used.fill(false); degree.fill(0);changed.fill(false);excluded.fill(false);bad.clear();edits.clear();
        for(int v:p)flip(v);
        check(a);check(b);
    }
    void walk(){
        if(nodes>=limit)return;
        nodes++;total++;
        if(bad.empty()){
            if(edits.empty())return;
            vector<int> k=edits;sort(k.begin(),k.end());k.insert(k.begin(),t);k.insert(k.begin(),s);
            if(!emitted.insert(k).second)return;
            vector<int> ordered{s};int last=-1;
            while(ordered.back()!=t){
                int v=ordered.back(),u=-1;
                for(int d=0;d<9;d++){int n=v^(1<<d);if(n!=last&&used[n]){assert(u==-1);u=n;}}
                assert(u>=0);last=v;ordered.push_back(u);assert(ordered.size()<=512);
            }
            cout<<"T "<<seed<<" "<<s<<" "<<t<<" "<<count(used.begin(),used.end(),true)<<" "<<ordered.size();
            for(int v:edits)cout<<" "<<v;cout<<"\n";
            return;
        }
        if(edits.size()>=budget)return;
        vector<int> branch;
        for(int v:bad){
            vector<int> choices;
            if(!used[v]){
                if(!changed[v]&&!excluded[v])choices.push_back(v);
            }else{
                if(v!=s&&v!=t&&!changed[v]&&!excluded[v])choices.push_back(v);
                int defect=degree[v]-want(v);
                vector<int> repair;
                for(int d=0;d<9;d++){
                    int n=v^(1<<d);
                    if((used[n]==(defect>0))&&!changed[n]&&!excluded[n]&&!(used[n]&&(n==s||n==t)))repair.push_back(n);
                }
                if(repair.size()>=abs(defect)&&edits.size()+abs(defect)<=budget)choices.insert(choices.end(),repair.begin(),repair.end());
            }
            if(choices.empty())return;
            if(branch.empty()||branch.size()>choices.size())branch=choices;
        }
        for(int v:branch){
            if(nodes>=limit)break;
            changed[v]=true;edits.push_back(v);flip(v);
            walk();flip(v);edits.pop_back();changed[v]=false;excluded[v]=true;
        }
        for(int v:branch)excluded[v]=false;
    }
    void run(int first){
        nodes=0;
        if(first>=0){changed[first]=true;edits.push_back(first);flip(first);}
        walk();
        if(first>=0){flip(first);edits.pop_back();changed[first]=false;}
        cutoffs+=nodes>=limit;
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    string mode=argv[1],word;int id=-1;
    while(cin>>word){id++; if(word=="-")continue;
        vector<int> p{0};for(char c:word)p.push_back(p.back()^(1<<(c-'0')));
        Trade q;q.seed=id;q.budget=stoi(argv[2]);q.limit=stoi(argv[3]);
        if(mode=="control"){
            vector<int> cut(p.begin(),p.end()-2);q.setup(cut,p.front(),p.back());q.run(-1);
        }else{
            q.setup(p,p.front(),p.back());
            for(int x=0;x<512;x++)if(x!=p.front()&&x!=p.back())q.run(x);
            if(mode=="move"){
                for(int side=0;side<2;side++){
                    int old=side?p.back():p.front(),keep=side?p.front():p.back();
                    for(int x=0;x<512;x++){
                        if(x==keep||__builtin_parity(unsigned(keep^x)))continue;
                        q.setup(p,keep,x);q.run(-1);
                    }
                }
            }
        }
        cout<<"D "<<id<<" "<<q.total<<" "<<q.cutoffs<<" "<<q.emitted.size()<<endl;
    }
}
