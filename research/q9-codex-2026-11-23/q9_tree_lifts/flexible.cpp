// Every donor step names one of the two flips in a lifted two-edge step.
// The partner coordinate may change independently at every occurrence.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <random>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using P=vector<int>;
bool valid(const P& p){for(int j=0;j<int(p.size());j++)for(int i=0;i<j;i++){
 int d=popcount(unsigned(p[i]^p[j]));if(!d||((d==1)!=(j==i+1)))return false;}return true;}
struct State{
 array<uint8_t,256> load{},ban{};
 array<int16_t,256> mate;
 array<uint16_t,105> seq{};
 int k=0,v=0,empty=256,safe=256;uint64_t hash=0;
 State(){mate.fill(-1);ban[0]=1;safe--;for(int b=1;b<512;b*=2){load[b>>1]++;empty--;}}
 void reserve(int odd){for(int b=1;b<512;b*=2){auto& z=ban[(odd^b)>>1];if(!z){z=1;safe--;}}}
 bool possible(int a,int b)const{return a!=b&&!ban[(v^a^b)>>1]&&(load[(v^a)>>1]==1||load[(v^b)>>1]==1);}
 void push(int a,int b){
    assert(possible(a,b));int o1=v^a,o2=v^b,x=v^a^b;
    bool first=load[o1>>1]==1,second=load[o2>>1]==1;
    for(int bit=1;bit<512;bit*=2){int y=x^bit;auto& n=load[y>>1];if(!n)empty--;
        if(n==2&&mate[y>>1]>=0){int other=mate[y>>1];mate[y>>1]=mate[other>>1]=-1;reserve(other);}
        n++;}
    if(first&&second){mate[o1>>1]=o2;mate[o2>>1]=o1;}else reserve(first?o1:o2);
    if(!ban[x>>1]){ban[x>>1]=1;safe--;}
    seq[++k]=x;v=x;
 }
 P witness()const{P p{0};for(int i=1;i<=k;i++){
    int u=seq[i-1],x=seq[i],z=x^u,a=z&-z,b=z^a;
    assert(a&&has_single_bit(unsigned(b)));
    int odd=load[(u^a)>>1]==2?u^a:u^b;assert(load[odd>>1]==2);
    p.push_back(odd);p.push_back(x);}
    assert(valid(p));return p;
 }
};
struct Cand{float score;uint64_t hash;int i,axis;};
#ifndef Q9_FLEX_LIBRARY
int main(int argc,char**argv){
 if(argc!=5)return 2;mt19937_64 rng(stoull(argv[1]));int width=stoi(argv[2]),runs=stoi(argv[3]),target=stoi(argv[4]);
 vector<string> words;string w;while(cin>>w)words.push_back(w);int best=-1;uint64_t expanded=0;
 array<array<uint64_t,9>,512> salts;for(auto& a:salts)for(auto& b:a)b=rng();
 for(int turn=0;turn<runs;turn++){int row=rng()%words.size();w=words[row];if(rng()%2)reverse(w.begin(),w.end());
    vector<State> cur(1);double ws=.1+(rng()%700)*.001,we=.2+(rng()%500)*.002,wr=1+(rng()%500)*.01,wl=(rng()%400)*.01;
    for(int t=0;t<int(w.size());t++){
        int d=w[t]-'0',a=1<<d,nd=w[min(t+1,int(w.size())-1)]-'0';
        vector<Cand> cand;unordered_set<uint64_t> seen;
        for(int i=0;i<int(cur.size());i++){auto& p=cur[i];for(int e=0;e<9;e++)if(p.possible(a,1<<e)){
            int x=p.v^a^(1<<e);uint64_t h=p.hash^salts[min(x,p.v)][min(d,e)]^(salts[max(x,p.v)][max(d,e)]);
            if(!seen.insert(h^salts[x][0]).second)continue;
            State next=p;next.push(a,1<<e);expanded++;
            int count=0;for(int c=1;c<512;c*=2)count+=next.possible(1<<nd,c);
            if(t+1<target/2&&!count&&t+1<best/2)continue;
            float noise=wr*double(rng()%1000000)/1000000.;
            cand.push_back({float(ws*next.safe+we*next.empty+wl*count+noise),h,i,e});
        }}
        if(cand.empty())break;
        if(cand.size()>width){nth_element(cand.begin(),cand.begin()+width,cand.end(),[](const Cand& a,const Cand& b){return a.score>b.score;});cand.resize(width);}
        vector<State> next;next.reserve(cand.size());
        for(auto& c:cand){auto& s=next.emplace_back(cur[c.i]);s.push(a,1<<c.axis);s.hash=c.hash;}
        if(2*(t+1)>best){best=2*(t+1);auto& s=next[0];P p=s.witness();
            if(best>=128||best>=target){cout<<"BEST "<<turn<<" "<<row<<" "<<best<<" "<<w.substr(0,t+1);for(int v:p)cout<<" "<<v;cout<<endl;}
            if(best>=target)return 0;}
        cur.swap(next);
    }
    if(turn%4==0)cout<<"AT "<<turn<<" "<<expanded<<" "<<best<<endl;
 }
}

#endif
