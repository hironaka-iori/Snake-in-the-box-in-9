#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Site=array<bool,256>;
using Simplex=array<int,9>;
struct Eval{
    int score=0,components=0,zero=0,one=0,edges=0,ports=0,excess=0,deficit=0;
    array<int,256> degree{},parent{},lo{},hi{};
    int root(int x){while(parent[x]!=x){parent[x]=parent[parent[x]];x=parent[x];}return x;}
};
Eval eval(const Site&e,const Simplex& t,bool odd){
    Eval v;array<int,256> count{},a{},b{};array<array<int,16>,256> adj;
    array<uint8_t,256> n{};for(int i=0;i<256;i++){v.parent[i]=i;if(e[i])for(int g:t){int z=i^g;if(count[z]==0)a[z]=i;else if(count[z]==1)b[z]=i;count[z]++;}}
    for(int z=0;z<256;z++){if(count[z]==1)v.ports++;if(count[z]!=2)continue;int x=a[z],y=b[z];bool seen=false;
        for(int j=0;j<n[x];j++)if(adj[x][j]==y){seen=true;break;}if(seen)continue;
        adj[x][n[x]++]=y;adj[y][n[y]++]=x;v.edges++;int rx=v.root(x),ry=v.root(y);if(rx!=ry)v.parent[rx]=ry;
    }
    int m=0;for(int x=0;x<256;x++)if(e[x]){m++;int k=v.degree[x]=n[x];v.zero+=k==0;v.one+=k==1;v.components+=v.root(x)==x;}
    int req=0;for(int x=0;x<256;x++)if(e[x]){
        int forced=0;for(int j=0;j<n[x];j++)forced+=n[adj[x][j]]<=2;
        if(forced>2){req+=forced-2;v.excess=max(v.excess,forced-2);}
    }
    v.deficit=max(0,2*v.zero+v.one-2);
    v.score=12*v.zero+6*max(0,v.one-2)+9*(v.components-1)+4*max(0,m-1-v.edges)+2*max(0,req-4)+3*max(0,v.excess-2)+6*(odd&&v.ports==0);
    return v;
}
bool basis(const Simplex&t){
    int piv[8]{};for(int i=1;i<9;i++){int x=t[i]^t[0];for(int p=7;p>=0;p--)if(x>>p&1){if(piv[p])x^=piv[p];else{piv[p]=x;break;}}if(!x)return false;}return true;
}
int main(int argc,char**argv){
    if(argc!=5)return 2;int goal=atoi(argv[1]),restarts=atoi(argv[2]),steps=atoi(argv[3]);mt19937 rng(atoi(argv[4]));auto randn=[&](int n){return (int)(rng()%n);};
    vector<string> words;string w;while(cin>>w)words.push_back(w);int need=goal/2+1,total=0,best=100000;
    unordered_set<string> reports;
    for(int r=0;r<restarts;r++){
        w=words[randn(words.size())];vector<int> path{0};for(char a:w)path.push_back(path.back()^(1<<(a-'0')));
        int parity=randn(2);Site e{};vector<int> pool;
        for(int i=parity;i<(int)path.size();i+=2){int x=path[i]&255;if(!e[x]){e[x]=true;pool.push_back(x);}}
        while((int)pool.size()>need){int k=randn(pool.size());e[pool[k]]=false;pool.erase(pool.begin()+k);}
        while((int)pool.size()<need){int x=randn(256);if(!e[x]){e[x]=true;pool.push_back(x);}}
        Simplex t{0,1,2,4,8,16,32,64,128};Eval state=eval(e,t,goal%2);Site beste=e;Simplex bestt=t;int local=state.score;
        for(int step=0;step<steps;step++){
            if(state.score==0){string id;for(int x=0;x<256;x++)if(e[x])id.push_back(char(x));Simplex key=t;sort(key.begin(),key.end());for(int a:key)id.push_back(char(a));
                if(reports.insert(id).second){cout<<"C "<<r<<" "<<step;for(int d:t)cout<<" "<<d;cout<<" sites";for(int i=0;i<256;i++)if(e[i])cout<<" "<<i;cout<<endl;total++;}
            }
            best=min(best,state.score);int typ=randn(100);Site next=e;Simplex nt=t;
            if(typ<13){
                int k=randn(9);do{nt[k]=randn(256);}while(!basis(nt));
            }else{
                int a=randn(256);while(!e[a])a=randn(256);
                if(typ<75)for(int j=0;j<12;j++){int q=randn(256);if(e[q]&&state.degree[q]<state.degree[a])a=q;}
                int b=randn(256);
                if(typ>=50&&typ<90)b=a^t[randn(9)]^t[randn(9)];
                if(typ>=90){int q=randn(256);while(!e[q])q=randn(256);b=q^t[randn(9)]^t[randn(9)];}
                while(e[b])b=randn(256);next[a]=false;next[b]=true;
            }
            Eval candidate=eval(next,nt,goal%2);double temp=1.9+4.*(1.-(step%300)/300.);
            if(candidate.score<=state.score||generate_canonical<double,32>(rng)<exp((state.score-candidate.score)/temp)){
                e=next;t=nt;state=candidate;if(state.score<local){local=state.score;beste=e;bestt=t;}
            }
            if(step%300==299&&(randn(3)!=0)){e=beste;t=bestt;state=eval(e,t,goal%2);}
        }
        cout<<"R "<<r<<" best "<<local<<" overall "<<best<<" candidates "<<total<<endl;
    }
}
