#pragma once
// Allow one specified cube edge to be a chord, then rethread all vertices of the other color.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <set>
#include <sstream>
#include <fstream>
#include <cassert>
using Path=vector<int>;
string encode(const Path& p){
    string w;for(int i=1;i<p.size();i++)w+=char('0'+countr_zero(unsigned(p[i]^p[i-1])));
    auto norm=[](string a){array<int,9> labels;labels.fill(-1);int count=0;for(auto& c:a){int d=c-'0';if(labels[d]<0)labels[d]=count++;c='0'+labels[d];}return a;};
    auto f=norm(w);reverse(w.begin(),w.end());return min(f,norm(w));
}
struct Repair{
    int a,b,cap;set<string>& known;ostream& output;uint64_t tests=0,graphs=0,unknown=0,positive=0,fresh=0,lifts=0;
    bool countOnly=false; uint64_t clean=0;
    bool run(Search& s){
        tests++;int n=s.fixed.size();int major=n==97;
        // Only the opposite-color endpoint sees a changed incidence mask.
        int fixedColor=popcount(unsigned(s.fixed[0]))%2;
        int x=(popcount(unsigned(a))%2==fixedColor)?a:b,y=x^a^b;
        if(s.slot[x]>=0)s.axes[y]^=x^y;
        bool hit=check(s,major);
        if(s.slot[x]>=0)s.axes[y]^=x^y;
        return hit;
    }
    bool check(Search& s,bool major){
        int n=s.fixed.size();array<int,512> degree{};int leaves=0,pairs=0;
        for(int v=0;v<512;v++){
            unsigned m=s.axes[v];int k=popcount(m);if(k==2)pairs++;else if(k==1){leaves++;if(major)continue;}else continue;
            while(m){degree[v^(1<<countr_zero(m))]++;m&=m-1;}
        }
        if(pairs<n-1||(!major&&leaves<2))return false;
        int low=0;for(int v:s.fixed){if(degree[v]<1)return false;low+=degree[v]==1;}
        if(low>(major?2:0))return false;
        Graph g(s.fixed,cap);graphs++;
        for(int v=0;v<512;v++){
            unsigned m=s.axes[v];int k=popcount(m);if(k!=2&&(major||k!=1))continue;
            int i=s.slot[v^(1<<countr_zero(m))];m&=m-1;
            int j=m?s.slot[v^(1<<countr_zero(m))]:g.dummy;g.add(i,j,v);
        }
        if(major)for(int i=0;i<n;i++)g.add(i,g.dummy,-1);
        vector<int8_t> state(g.edges.size());
        auto orders=[&](auto&& self,vector<int8_t> assignment)->bool{
            if(g.nodes>=cap){unknown++;return false;}
            g.witness.clear();
            int result=g.visit(assignment);
            if(result<0){unknown++;return false;}
            if(!result)return false;
            positive++;
            Path used;
            int previous=g.dummy;
            auto append=[&](int next){
                for(int id:g.adj[previous]){
                    auto link=g.edges[id];
                    if((link.a^link.b^previous)==next){used.push_back(id);previous=next;return;}
                }
                abort();
            };
            for(int i=major?0:1;i<g.witness.size();i+=2)append(s.slot[g.witness[i]]);
            append(g.dummy);
            if(lift(s,major,g.witness))return true;
            for(int id:used)if(!assignment[id]){
                assignment[id]=-1;
                if(self(self,assignment))return true;
                if(g.nodes>cap)return false;
                assignment[id]=1;
            }
            return false;
        };
        return orders(orders,state);
    }
    bool lift(Search& s,bool major,const Path& witness){
        auto p=witness;int parity=major?1:0;vector<int> sites;vector<Path> opts;
        for(int i=parity;i<p.size();i+=2){
            int v=i?p[i-1]:p[i+1];Path choices;
            for(int d=0;d<9;d++){
                int z=v^(1<<d);unsigned m=s.axes[z];if(!(m&(1<<d)))continue;
                if(i>0&&i+1<p.size()){
                    unsigned other=z^p[i+1];if(!has_single_bit(other)||popcount(m)!=2||!(m&other))continue;
                }else if(popcount(m)!=1)continue;
                choices.push_back(z);
            }
            if(choices.size()>1){sites.push_back(i);opts.push_back(choices);}
        }
        auto enumerate=[&](auto&& self,int pos)->bool{
            if(pos<sites.size()){for(int v:opts[pos]){p[sites[pos]]=v;if(self(self,pos+1))return true;}return false;}
            lifts++;assert(p.size()==2*s.fixed.size()+(major?-1:1));int chords=0;
            for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){
                int d=popcount(unsigned(p[i]^p[j]));assert(d && (i!=j+1||d==1));
                if(i!=j+1 && d==1){assert((p[i]==a&&p[j]==b)||(p[i]==b&&p[j]==a));chords++;}
            }
            if(countOnly){clean+=chords==0;return false;}
            if(!chords){cout<<"FOUND";for(int v:p)cout<<" "<<v;cout<<endl;return true;}
            assert(chords==1);auto w=encode(p);if(known.insert(w).second){fresh++;output<<w<<endl;}return false;
        };
        return enumerate(enumerate,0);
    }
};
