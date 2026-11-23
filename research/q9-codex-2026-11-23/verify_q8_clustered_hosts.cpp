// Independent verification. Filter by the intersection common to every member of
// a group, then check candidate hosts by hitting the original induced K1,3s.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <sstream>
#include <vector>
using namespace std;
using Bits=array<uint64_t,4>;using P=vector<int>;
struct Member{P points;array<Bits,256> translated{};};
struct Group{vector<Member> donors;Bits core;int biggest=0;array<Bits,256> shifted{};
 Group(){core.fill(~uint64_t(0));}
};
void mark(Bits& b,int x){b[x/64]|=uint64_t(1)<<(x%64);}
bool has(const Bits& b,int x){return (b[x/64]>>(x%64))&1;}
int common(const Bits& a,const Bits& b){
 int n=0;for(int i=0;i<4;i++)n+=popcount(a[i]&b[i]);return n;
}
struct Audit{
 array<bool,512> in{},omit{};P verts;vector<array<int,4>> claws;int goal,extra,dim=9;
 bool testLinear(){
    array<bool,512> seen{};int top[4]{};
    for(int v:verts)if(!seen[v]&&!omit[v]){
        int size=0,ends=0;P queue{v};seen[v]=true;
        for(int i=0;i<queue.size();i++){
            int deg=0;for(int j=0;j<dim;j++){int u=queue[i]^(1<<j);if(!in[u]||omit[u])continue;deg++;if(!seen[u]){queue.push_back(u);seen[u]=true;}}
            assert(deg<=2);ends+=deg<2;size++;
        }
        int remaining=size;
        for(int h=0;h<=extra;h++)if(remaining>top[h])swap(remaining,top[h]);
        if(size-int(ends==0)>=goal+1)return true;
    } potential=extra+accumulate(top,top+extra+1,0);return false;
 }
 int potential=0;
 bool visit(int pos,int left){
    while(pos<claws.size()){
        auto star=claws[pos++];if(any_of(star.begin(),star.end(),[&](int x){return omit[x];}))continue;
        if(!left)return false;
        for(int x:star){omit[x]=true;bool ok=visit(pos,left-1);omit[x]=false;if(ok)return true;}
        return false;
    }
    if(testLinear())return true;
    if(!extra||potential<goal+1)return false;
    // A new vertex can only connect the components through its remaining
    // neighbors. If there are too many, every remaining deletion has to
    // remove one of them after choosing the (at most two) neighbors to keep.
    --extra;
    for(int v=0;v<(1<<dim);v++)if(!in[v]){
        P near;for(int j=0;j<dim;j++){int u=v^(1<<j);if(in[u]&&!omit[u])near.push_back(u);}
        if(near.empty()||near.size()>left+2)continue;
        int old=claws.size();
        for(int a=0;a<near.size();a++)for(int b=0;b<a;b++)for(int c=0;c<b;c++)claws.push_back({v,near[a],near[b],near[c]});
        for(int u:near){
            P adj;for(int j=0;j<dim;j++){int x=u^(1<<j);if(in[x]&&!omit[x])adj.push_back(x);}
            if(adj.size()==2)claws.push_back({u,v,adj[0],adj[1]});
        }
        in[v]=true;verts.push_back(v);bool ok=visit(old,left);verts.pop_back();in[v]=false;claws.resize(old);
        if(ok){++extra;return true;}
    }
    ++extra;return false;
 }
 bool run(P p,int g,int slack,int allow){
    verts=std::move(p);goal=g;extra=allow;for(int v:verts)in[v]=true;
    for(int v:verts){P star{v};for(int j=0;j<dim;j++)if(in[v^(1<<j)])star.push_back(v^(1<<j));
        assert(star.size()<=4);if(star.size()==4)claws.push_back({v,star[1],star[2],star[3]});}
    return visit(0,slack);
 }
};
#ifndef Q8_AUDIT_LIBRARY
int main(int argc,char**argv){
 if(argc!=3)return 2;int goal=stoi(argv[1]),extra=stoi(argv[2]);vector<Group> groups;string l;
 while(getline(cin,l)){istringstream ss(l);int g,id,x;ss>>g>>id;if(g==groups.size())groups.emplace_back();
    auto& a=groups[g];auto& m=a.donors.emplace_back();while(ss>>x)m.points.push_back(x);
    for(int v:m.points)for(int t=0;t<256;t++)mark(m.translated[t],v^t);
    for(int i=0;i<4;i++)a.core[i]&=m.translated[0][i];a.biggest=max(a.biggest,int(m.points.size()));
 }
 for(auto &g:groups)for(int x=0;x<256;x++)if(has(g.core,x))for(int t=0;t<256;t++)mark(g.shifted[t],x^t);
 uint64_t pairs=0,eligible=0,survive=0;
 for(int i=0;i<groups.size();i++){auto& a=groups[i];
 for(int j=i;j<groups.size();j++){auto& b=groups[j];int maxCross=2*(a.biggest+b.biggest-goal-1+extra)+1;if(maxCross<0)continue;
    for(int u=0;u<a.donors.size();u++)for(int v=(i==j?u:0);v<b.donors.size();v++)pairs+=int(a.donors[u].points.size()+b.donors[v].points.size())+extra>=goal+1;
    vector<Bits> moved(b.donors.size());P corePoints;
    for(int x=0;x<256;x++)if(has(b.core,x))corePoints.push_back(x);
    array<int,8> axes{0,1,2,3,4,5,6,7};
    do{
        array<int,256> img{};for(int d=0;d<8;d++)for(int x=0;x<(1<<d);x++)img[x+(1<<d)]=img[x]+(1<<axes[d]);
        Bits core{};for(int x:corePoints)mark(core,img[x]);bool ready=false;
        for(int t=0;t<256;t++)if(common(core,a.shifted[t])<=maxCross){
            if(!ready){for(int v=0;v<b.donors.size();v++){moved[v]={};for(int x:b.donors[v].points)mark(moved[v],img[x]);}ready=true;}
            for(int u=0;u<a.donors.size();u++)for(int v=(i==j?u:0);v<b.donors.size();v++){
                auto &left=a.donors[u],&right=b.donors[v];int slack=int(left.points.size()+right.points.size())+extra-goal-1;
                int cross=common(left.translated[t],moved[v]);if(slack<0||(!cross&&!extra)||cross>2*slack+1)continue;
                eligible++;
#ifdef Q8_COUNT_FILTER_ONLY
                continue;
#endif
                P host=left.points;for(int y:right.points)host.push_back(256+(img[y]^t));
                Audit audit;if(audit.run(std::move(host),goal,slack,extra)){survive++;cout<<"FEASIBLE "<<i<<" "<<j<<" "<<u<<" "<<v<<" "<<t<<endl;return 0;}
            }
        }
    }while(next_permutation(axes.begin(),axes.end()));
 }cout<<"AT "<<i+1<<" "<<pairs<<" "<<eligible<<endl;}
#ifdef Q8_COUNT_FILTER_ONLY
 cout<<"FILTER "<<goal<<" "<<extra<<" "<<pairs<<" "<<eligible<<endl;return 0;
#endif
 cout<<"DONE "<<goal<<" "<<extra<<" "<<pairs<<" "<<eligible<<" "<<survive<<endl;
}

#endif
