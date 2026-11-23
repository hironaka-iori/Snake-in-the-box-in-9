// Exact decision in a specified vertex domain: every induced path must avoid a K1,3.
#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using Mask=bitset<512>;using Path=vector<int>;
struct Decision{
    int target,cap;uint64_t nodes=0;bool cutoff=false;Path witness;
    array<array<int,9>,512> nb{};
    Decision(int n,int k):target(n),cap(k){for(int x=0;x<512;x++)for(int j=0;j<9;j++)nb[x][j]=x^(1<<j);}
    bool dfs(Mask available,Mask keep,Path vertices){
        if(++nodes>cap){cutoff=true;return false;}
        if(vertices.size()<target)return false;
        // Any solution is contained in a single connected component of the remaining graph.
        Path queue;queue.reserve(vertices.size());Mask left=available;
        for(int start:vertices)if(left[start]){
            queue.clear();queue.push_back(start);left.reset(start);
            for(size_t i=0;i<queue.size();i++)for(int y:nb[queue[i]])if(left[y]){left.reset(y);queue.push_back(y);}
            if(queue.size()==vertices.size())break;
            if(queue.size()>=target){
                Mask component;for(int v:queue)component.set(v);
                if(dfs(component,keep&component,queue))return true;
                if(cutoff)return false;
            }
            if(left.count()<target)return false;
        }
        array<int,512> degree{};int center=-1,tip=-1,odd=0;
        for(int x:vertices){
            int d=0;for(int y:nb[x])d+=available[y];degree[x]=d;odd+=popcount(unsigned(x))%2;
            if(d<=1)tip=x;
            if(d>=3 && (center<0||d>degree[center]))center=x;
        }
        if(2*min(odd,int(vertices.size())-odd)+1<target)return false;
        if(center<0){
            bool cycle=tip<0;
            if(int(vertices.size())-cycle<target)return false;
            Path seq;int v=cycle?vertices[0]:tip;
            while(v>=0 && seq.size()<target){seq.push_back(v);available.reset(v);
                int next=-1;for(int y:nb[v])if(available[y]){next=y;break;}v=next;}
            if(seq.size()!=target)return false;
            for(int i=0;i<target;i++)for(int j=0;j<i;j++)assert((popcount(unsigned(seq[i]^seq[j]))==1)==(j+1==i));
            witness=std::move(seq);return true;
        }
        int slack=int(vertices.size())-target;
        if(degree[center]-2>slack){
            if(keep[center]||!slack)return false;
            available.reset(center);vertices.erase(find(vertices.begin(),vertices.end(),center));
            return dfs(available,keep,vertices);
        }
        Mask packed;int lower=0;
        for(int x:vertices)if(degree[x]>=3&&!packed[x]){
            array<int,3> arms;int n=0;for(int y:nb[x])if(available[y]&&!packed[y]){arms[n++]=y;if(n==3)break;}
            if(n==3){packed.set(x);for(int y:arms)packed.set(y);if(++lower>slack)return false;}
        }
        Path neighbors;for(int y:nb[center])if(available[y])neighbors.push_back(y);
        sort(neighbors.begin(),neighbors.end(),[&](int a,int b){return (keep[a]*16+degree[a])>(keep[b]*16+degree[b]);});
        array<int,4> choice{center,neighbors[0],neighbors[1],neighbors[2]};
        for(int x:choice)if(!keep[x]){
            Mask child=available;child.reset(x);
            Path rest=vertices;rest.erase(find(rest.begin(),rest.end(),x));
            if(dfs(child,keep,std::move(rest)))return true;
            if(cutoff)return false;
            keep.set(x);
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=3)return 2;
    int target=stoi(argv[1])+1,cap=stoi(argv[2]);string line;
    while(getline(cin,line)){
        istringstream in(line);Path vs;Mask active;int x;
        while(in>>x){if(x<0||x>=512||active[x])return 2;active[x]=1;vs.push_back(x);}
        Decision query(target,cap);
        if(query.dfs(active,Mask{},vs)){cout<<"FOUND";for(int v:query.witness)cout<<" "<<v;}
        else cout<<(query.cutoff?"UNKNOWN":"NO")<<" "<<query.nodes;
        cout<<endl;
    }
}
