#define Q9_FRAGMENT_LIBRARY
#include "q9_two_fragments.cpp"
#include <numeric>

using Path=vector<int>;
using Bits=array<uint64_t,8>;
Path decodeWord(const string& w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));return p;}

struct Shape {
    Path p,axes;
    int root=0,dimension;
    array<vector<pair<int,bool>>,10> added;
    Shape(Path points,int dim):p(move(points)),dimension(dim){
        int size=1<<dim,mask=0;
        for(int v:p)mask|=v^p.front();
        long best=-1;
        for(int rootCandidate:p){
            vector<int> inside(size),last(size);
            vector<long> score(size);
            for(int v:p)inside[v^rootCandidate]=1;
            for(int b=1;b<size;b*=2)for(int m=0;m<size;m++)if(m&b)inside[m]+=inside[m^b];
            for(int m=1;m<size;m++)if(!(m&~mask)){
                long prev=-1;
                for(int ds=m;ds;ds&=ds-1){
                    int bit=ds&-ds;
                    if(score[m^bit]>prev){prev=score[m^bit];last[m]=bit;}
                }
                score[m]=prev+long(inside[m])*(dim-popcount(unsigned(m))+1);
            }
            if(score[mask]>best){
                best=score[mask];root=rootCandidate;axes.clear();
                for(int m=mask;m;m^=last[m])axes.push_back(countr_zero(unsigned(last[m])));
                reverse(axes.begin(),axes.end());
            }
        }
        for(int v:p){
            int d=0,m=v^root;
            for(int i=0;i<int(axes.size());i++)if(m&(1<<axes[i]))d=i+1;
            added[d].push_back({m,v==p.front()||v==p.back()});
        }
    }
};

struct Embed {
    int dim,size,blocks;
    array<Bits,512> inner{},end{};
    array<int,512> image{};
    array<int,512> neighbours{};
    JoinSearch search;
    const Shape* shape=nullptr;
    Path fixed;
    uint64_t assignments=0,admitted=0,direct=0;
    bool census=false;
    set<Path> censusPaths;
    explicit Embed(int d,int goal):dim(d),size(1<<d),blocks((size+63)/64){search.extension.dimensions=d;search.extension.goal=goal;}
    void setFirst(const Path&a){
        fixed=a;array<bool,512> used{};neighbours.fill(0);
        for(int v:a){used[v]=true;for(int j=0;j<dim;j++)neighbours[v^(1<<j)]++;}
        for(int m=0;m<size;m++){
            inner[m].fill(0);end[m].fill(0);
            for(int v=0;v<size;v++)if(!used[v]){
                int t=m^v;
                uint64_t bit=uint64_t(1)<<(t%64);
                if(!neighbours[v]){inner[m][t/64]|=bit;end[m][t/64]|=bit;}
                else if(neighbours[v]==1&&(JoinSearch::adjacent(v,a.front())||JoinSearch::adjacent(v,a.back())))end[m][t/64]|=bit;
            }
        }
    }
    bool branch(int k,int unused,const Bits& choices){
        assignments++;
        if(k==int(shape->axes.size())){
            for(int j=0;j<blocks;j++)for(uint64_t bits=choices[j];bits;bits&=bits-1){
                int t=j*64+countr_zero(bits);
                int edges=neighbours[t^image[shape->p.front()^shape->root]]+neighbours[t^image[shape->p.back()^shape->root]];
                if(edges>1)continue;
                admitted++;direct+=edges;
                search.first=fixed;search.second.clear();
                for(int v:shape->p)search.second.push_back(t^image[v^shape->root]);
                if(census){censusPaths.insert(search.second);continue;}
                if(search.placed(edges==1))return true;
            }
            return false;
        }
        int source=1<<shape->axes[k];
        // Only offsets needed at this layer depend on the new bit. Fill all
        // subsets of previously assigned axes for use by subsequent layers.
        int prefix=0;for(int i=0;i<k;i++)prefix|=1<<shape->axes[i];
        for(int rest=unused;rest;rest&=rest-1){
            int dest=rest&-rest; Bits next=choices; bool possible=true;
            for(auto [m,tip]:shape->added[k+1]){
                int v=image[m^source]|dest;
                const Bits& permitted=tip?end[v]:inner[v];
                uint64_t live=0;
                for(int j=0;j<blocks;j++){next[j]&=permitted[j];live|=next[j];}
                if(!live){possible=false;break;}
            }
            if(!possible)continue;
            for(int m=prefix;;m=(m-1)&prefix){image[m|source]=image[m]|dest;if(!m)break;}
            if(branch(k+1,unused^dest,next))return true;
        }
        return false;
    }
    bool run(const Shape& s){
        shape=&s;image[0]=0;
        return branch(0,size-1,s.added[0][0].second?end[0]:inner[0]);
    }
};

#ifndef Q9_MIXED_CHECK
int main(int argc,char**argv){
    if(argc<5)return 2;
    int n=stoi(argv[1]),target=stoi(argv[2]),offset=stoi(argv[3]);
    set<string> words;
    for(int i=4;i<argc;i++){
        ifstream f(argv[i]);if(!f)throw runtime_error("input");string w;
        while(f>>w){if(int(w.size())<n+offset)throw runtime_error("short input");words.insert(canonical(w.substr(offset,n)));words.insert(canonical(w.substr(w.size()-offset-n,n)));}
    }
    vector<Shape> shapes;
    for(auto&w:words){auto p=decodeWord(w);
        for(size_t j=0;j<p.size();j++)for(size_t i=0;i<j;i++)if(p[i]==p[j]||(JoinSearch::adjacent(p[i],p[j])!=(i+1==j)))throw runtime_error("invalid input");
        shapes.emplace_back(move(p),9);
    }
    Embed embed(9,target);uint64_t pairs=0;
    cout<<"START "<<target<<" "<<n<<" "<<offset<<" "<<shapes.size()<<endl;
    for(size_t i=0;i<shapes.size();i++){
        embed.setFirst(shapes[i].p);
        for(size_t j=i;j<shapes.size();j++){pairs++;if(embed.run(shapes[j])){cout<<"PAIR "<<i<<" "<<j<<endl;return 0;}}
        cout<<"AT "<<i+1<<" "<<pairs<<" "<<embed.admitted<<" "<<embed.search.extension.nodes<<endl;
    }
    cout<<"DONE "<<pairs<<" "<<embed.admitted<<" "<<embed.direct<<" "<<embed.assignments<<" "<<embed.search.bridgeNodes<<" "<<embed.search.extension.nodes<<endl;
}
#endif
