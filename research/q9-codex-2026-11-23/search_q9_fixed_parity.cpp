// Search Q9 snakes with 96 prescribed vertices of one parity.
// Compress eligible opposite-parity vertices into graph edges and end choices.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Link {int a,b,via;};
struct Graph {
    int n,dummy;
    vector<Link> edges;
    vector<vector<int>> adj;
    vector<int> label,witness;
    int nodes=0, limit;
    explicit Graph(vector<int> values,int cap):n(int(values.size())+1),dummy(n-1),adj(n),label(values),limit(cap){}
    void add(int a,int b,int via){
        if(a==b)return;
        for(int id:adj[a]){
            const auto &e=edges[id];if((e.a==a && e.b==b)||(e.a==b && e.b==a))return;
        }
        int id=edges.size();edges.push_back({a,b,via});adj[a].push_back(id);adj[b].push_back(id);
    }
    int visit(vector<int8_t> state){
        if(++nodes>limit)return -1;
        bool changed;
        do{
            changed=false;
            for(int v=0;v<n;v++){
                int yes=0,open=0;
                for(int e:adj[v]){yes+=state[e]==1;open+=state[e]==0;}
                if(yes>2||yes+open<2)return 0;
                if(open && (yes==2 || yes+open==2)){
                    for(int e:adj[v])if(!state[e])state[e]=yes==2?-1:1;
                    changed=true;
                }
            }
        }while(changed);
        vector<int> parent(n),size(n,1);
        for(int i=0;i<n;i++)parent[i]=i;
        auto root=[&](int x){while(parent[x]!=x)x=parent[x];return x;};
        for(int i=0;i<int(edges.size());i++)if(state[i]==1){
            int a=root(edges[i].a),b=root(edges[i].b);
            if(a==b){
                if(size[a]!=n)return 0;
                int v=dummy,last=-1;
                do{
                    int next=-1;for(int e:adj[v])if(e!=last && state[e]==1){next=e;break;}
                    if(next<0)abort();
                    const auto &edge=edges[next];
                    if(edge.via>=0)witness.push_back(edge.via);
                    v=edge.a^edge.b^v;
                    if(v!=dummy)witness.push_back(label[v]);
                    last=next;
                }while(v!=dummy);
                return 1;
            }
            parent[b]=a;size[a]+=size[b];
        }
        int branch=-1,best=1000000;
        for(int v=0;v<n;v++){
            int open=0,pick=-1;
            for(int id:adj[v])if(!state[id]){open++;pick=id;}
            if(open && open<best){best=open;branch=pick;}
        }
        if(branch<0)return 0;
        state[branch]=1;
        int first=visit(state);
        if(first!=0)return first;
        state[branch]=-1;
        return visit(state);
    }
};
struct Search {
    vector<int> fixed;
    array<int,512> slot,axes{};
    int cap;bool majority;
    uint64_t tested=0,low=0,dead=0,unknown=0;
    explicit Search(vector<int> a,int limit,bool fixed_majority=false):fixed(a),cap(limit),majority(fixed_majority){
        slot.fill(-1);
        for(int i=0;i<int(a.size());i++)toggle(a[i],i,true);
    }
    void toggle(int x,int i,bool on){
        slot[x]=on?i:-1;
        for(int d=0;d<9;d++)axes[x^(1<<d)]^=1<<d;
    }
    bool test(){
        tested++;
        int color=popcount(unsigned(fixed[0]))%2;
        array<int,512> options{};int leaves=0;
        for(int v=0;v<512;v++){
            int m=axes[v],count=popcount(unsigned(m));
            if(count>2)continue;
            if(count==1){leaves++;if(majority)continue;}
            while(m){int d=countr_zero(unsigned(m));m&=m-1;options[v^(1<<d)]++;}
        }
        if(majority){
            int tips=0;
            for(int x:fixed){if(!options[x]){low++;return false;} tips+=options[x]==1;}
            if(tips>2){low++;return false;}
        }else if(leaves<2 || any_of(fixed.begin(),fixed.end(),[&](int x){return options[x]<2;})){low++;return false;}
        Graph g(fixed,cap);
        for(int v=0;v<512;v++){
            int m=axes[v],count=popcount(unsigned(m));
            if(count!=2 && (majority || count!=1))continue;
            int a=slot[v^(1<<countr_zero(unsigned(m)))];m&=m-1;
            int b=m?slot[v^(1<<countr_zero(unsigned(m)))]:g.dummy;
            if(a<0||b<0||popcount(unsigned(v))%2==color)abort();
            g.add(a,b,v);
        }
        if(majority)for(int j=0;j<int(fixed.size());j++)g.add(j,g.dummy,-1);
        int ret=g.visit(vector<int8_t>(g.edges.size()));
        if(ret<0){unknown++;return false;}
        if(!ret){dead++;return false;}
        const auto &p=g.witness;
        if(int(p.size())!=2*int(fixed.size())+(majority?-1:1))abort();
        for(int i=0;i<int(p.size());i++)for(int j=0;j<i;j++){
            int d=popcount(unsigned(p[i]^p[j]));
            if(d==0 || (d==1)!=(i==j+1))abort();
        }
        cout<<"FOUND";for(int v:p)cout<<" "<<v;cout<<"\n";return true;
    }
};
#ifndef Q9_PARITY_LIBRARY
int main(int argc,char**argv){
    if(argc>1 && (string(argv[1])=="--sets" || string(argv[1])=="--majority-sets")){
        int n=0;
        while(cin>>n){
            if(n<2 || n>255)return 2;
            vector<int> values(n);array<bool,512> seen{};
            for(int i=0;i<n;i++){
                int x;if(!(cin>>x) || x<0 || x>=512 || seen[x])return 3;
                values[i]=x;seen[x]=true;
                if(popcount(unsigned(x^values[0]))%2)return 4;
            }
            Search s(values,100000,string(argv[1])=="--majority-sets");
            if(!s.test())cout<<(s.unknown?"UNKNOWN":"NO")<<"\n";
        }
        return 0;
    }
    if(argc>1 && string(argv[1])=="--majority"){
        const int removed=argc>2?atoi(argv[2]):0;
        if(removed<0 || removed>1)return 2;
        uint64_t tested=0,skipped=0,low=0,dead=0,unknown=0;
        vector<int> p(192);
        while(cin>>p[0]){
            for(int i=1;i<192;i++)if(!(cin>>p[i]))return 3;
            for(int i=0;i<192;i++){
                if(p[i]<0 || p[i]>=512)return 4;
                for(int j=0;j<i;j++){
                    int d=popcount(unsigned(p[i]^p[j]));
                    if(!d || (d==1)!=(i==j+1))return 4;
                }
            }
            for(int side=0;side<2;side++){
                vector<int> a;
                for(int i=side;i<192;i+=2)a.push_back(p[i]);
                Search s(a,50000,true);
                vector<int> extras;
                for(int x=0;x<512;x++)if(s.slot[x]<0 && popcount(unsigned(x^a[0]))%2==0)extras.push_back(x);
                int end_slot=a.size();s.fixed.push_back(-1);
                for(int i=0;i<(removed?end_slot:1);i++){
                    if(removed)s.toggle(a[i],i,false);
                    vector<int> candidates;
                    for(int x:extras){
                        // An endpoint still needs one opposite-parity connector;
                        // adding more vertices can only shrink this availability.
                        int count=0;
                        for(int d=0;d<9;d++)count+=popcount(unsigned(s.axes[x^(1<<d)]))<=1;
                        if(count)candidates.push_back(x);
                    }
                    auto pairs=[](uint64_t n){return n*(n-1)/2;};
                    skipped+=removed?pairs(extras.size())-pairs(candidates.size()):extras.size()-candidates.size();
                    for(unsigned h=0;h<candidates.size();h++){
                        int x=candidates[h];s.fixed[end_slot]=x;s.toggle(x,end_slot,true);
                        if(!removed){if(s.test())return 0;}
                        else for(unsigned k=h+1;k<candidates.size();k++){
                            int y=candidates[k];s.fixed[i]=y;s.toggle(y,i,true);
                            if(s.test())return 0;
                            s.toggle(y,i,false);
                        }
                        s.toggle(x,end_slot,false);
                    }
                    if(removed){s.fixed[i]=a[i];s.toggle(a[i],i,true);}
                }
                tested+=s.tested;low+=s.low;dead+=s.dead;unknown+=s.unknown;
            }
        }
        cout<<"majority tests "<<tested<<" prefiltered "<<skipped<<" low_degree "<<low
            <<" exhausted "<<dead<<" unresolved "<<unknown<<"\n";
        return 0;
    }
    int swaps=argc>1?atoi(argv[1]):1,cap=argc>2?atoi(argv[2]):2000;
    int nread=argc>3?atoi(argv[3]):192;
    const bool use_larger_side=argc>4 && string(argv[4])=="--larger-side";
    if((swaps<0||swaps>2)||cap<1||nread<4||nread>512)return 2;
    vector<int>p(nread);
    uint64_t tested=0,low=0,dead=0,unknown=0,skipped=0;
    while(cin>>p[0]){
        for(int i=1;i<nread;i++)if(!(cin>>p[i]))return 3;
        for(int i=0;i<nread;i++){
            if(p[i]<0||p[i]>=512)return 4;
            for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));if(!d||(d==1)!=(i==j+1))return 4;}
        }
        for(int side=0;side<2;side++){
            if(nread%2 && side!=(use_larger_side?0:1))continue;
            vector<int>a;
            for(int i=side;i<nread;i+=2)a.push_back(p[i]);
            Search s(a,cap);
            if(s.test())return 0;
            if(swaps==1){
                vector<int>extras;
                for(int x=0;x<512;x++)if(s.slot[x]<0 && popcount(unsigned(x^a[0]))%2==0)extras.push_back(x);
                for(int i=0;i<int(a.size());i++){
                    s.toggle(a[i],i,false);
                    for(int x:extras){
                        s.fixed[i]=x;s.toggle(x,i,true);
                        if(s.test())return 0;
                        s.toggle(x,i,false);
                    }
                    s.fixed[i]=a[i];s.toggle(a[i],i,true);
                }
            }
            if(swaps==2){
                vector<int> extras;
                for(int x=0;x<512;x++)if(s.slot[x]<0 && popcount(unsigned(x^a[0]))%2==0)extras.push_back(x);
                for(int i=0;i<int(a.size());i++){
                    s.toggle(a[i],i,false);
                    for(int j=i+1;j<int(a.size());j++){
                        s.toggle(a[j],j,false);
                        // Every newly selected vertex must have two distinct neighbors
                        // with at most one neighbor already in the retained parity set.
                        array<int,512> available{};
                        for(int v=0;v<512;v++)if(popcount(unsigned(s.axes[v]))<=1){
                            for(int d=0;d<9;d++)available[v^(1<<d)]++;
                        }
                        vector<int> candidates;
                        for(int x:extras)if(available[x]>=2)candidates.push_back(x);
                        skipped+=(extras.size()*(extras.size()-1)-candidates.size()*(candidates.size()-1))/2;
                        for(unsigned h=0;h<candidates.size();h++){
                            int x=candidates[h];s.fixed[i]=x;s.toggle(x,i,true);
                            for(unsigned k=h+1;k<candidates.size();k++){
                                int y=candidates[k];s.fixed[j]=y;s.toggle(y,j,true);
                                if(s.test())return 0;
                                s.toggle(y,j,false);
                            }
                            s.toggle(x,i,false);
                        }
                        s.fixed[j]=a[j];s.toggle(a[j],j,true);
                    }
                    s.fixed[i]=a[i];s.toggle(a[i],i,true);
                }
            }
            tested+=s.tested;low+=s.low;dead+=s.dead;unknown+=s.unknown;
        }
    }
    cout<<"tests "<<tested<<" prefiltered "<<skipped<<" low_degree "<<low<<" exhausted "<<dead<<" unresolved "<<unknown<<"\n";
}
#endif
