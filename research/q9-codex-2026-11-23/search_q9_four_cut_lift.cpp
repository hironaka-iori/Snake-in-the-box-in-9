// Recombine five projected path fragments in all orders around four cuts.
// For each resulting projection, reuse the exact binary layer recoloring DP.
#define main recolor_entry_point
#include "search_q9_recolor_projection.cpp"
#undef main
#include <unordered_set>
struct Rejoin {
    Run &solver;
    int gap;
    long long cycles=0, orders=0, novel=0;
    std::unordered_set<std::string> unique;
    std::string signature(const P& path) {
        std::string f, r;
        int order[8], n=0;
        std::fill(order,order+8,-1);
        for(int i=1;i<(int)path.size();++i) {
            int d=__builtin_ctz(path[i]^path[i-1]); if(order[d]<0)order[d]=n++;
            f.push_back('0'+order[d]);
        }
        n=0;std::fill(order,order+8,-1);
        for(int i=(int)path.size()-1;i>=1;--i){
            int d=__builtin_ctz(path[i]^path[i-1]);if(order[d]<0)order[d]=n++;
            r.push_back('0'+order[d]);
        }
        return std::min(f,r);
    }
    void evaluate(const P& p) {
        const int n=p.size();
        std::array<int,256> pos;pos.fill(-1);
        for(int i=0;i<n;i++){if(pos[p[i]]>=0)return;pos[p[i]]=i;}
        std::vector<std::vector<int>> contact(n);
        for(int a=0;a<n;a++)for(int d=0;d<8;d++){
            int b=pos[p[a]^(1<<d)];if(b>=0)contact[a].push_back(b);
        }
        // Walk an alternating cycle of four old edges and four new contacts.
        // Restrict the initial cut to the minimum and orient it uniquely.
        for(int first=0;first+1<n;first++){
            int edges[4]={first,0,0,0}, links[4][2]{};
            auto grow=[&](auto&& self,int used,int tip)->void {
                if(used==4){
                    if(abs(tip-first-1)<=1 || __builtin_popcount(unsigned(p[tip]^p[first+1]))!=1)return;
                    links[3][0]=tip;links[3][1]=first+1;cycles++;
                    int adj[256][2],deg[256]{};
                    auto add=[&](int x,int y){adj[x][deg[x]++]=y;adj[y][deg[y]++]=x;};
                    for(int i=0;i+1<n;++i)if(std::find(edges,edges+4,i)==edges+4)add(i,i+1);
                    for(auto& link:links)add(link[0],link[1]);
                    P result;int prev=-1,v=0;
                    while(v>=0){
                        result.push_back(p[v]);int next=-1;
                        for(int j=0;j<deg[v];j++)if(adj[v][j]!=prev)next=adj[v][j];
                        prev=v;v=next;
                    }
                    if((int)result.size()!=n)return;
                    orders++;
                    if(unique.insert(signature(result)).second){solver.eval(result);novel++;}
                    return;
                }
                for(int other:contact[tip]){
                    if(abs(other-tip)<=1)continue;
                    for(int e:{other,other-1}){
                        if(e<=first||e+1>=n)continue;
                        bool ok=true;for(int k=0;k<used;k++)if(abs(edges[k]-e)<gap)ok=false;
                        if(!ok)continue;
                        edges[used]=e;
                        links[used-1][0]=tip;links[used-1][1]=other;
                        self(self,used+1,2*e+1-other);
                    }
                }
            };
            grow(grow,1,first);
        }
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    Run r(atoi(argv[1]),23,0,190);Rejoin j{r,atoi(argv[2])};int cap=atoi(argv[3]);
    std::string line;int rows=0;
    while(std::getline(std::cin,line)&&rows<cap){
        if(line.find(' ')!=std::string::npos)line=line.substr(line.rfind(' ')+1);
        if(line.empty())continue;
        P p{0};for(char c:line){if(c<'0'||c>'7')return 3;p.push_back(p.back()^(1<<(c-'0')));}
        j.evaluate(p);rows++;
    }
    std::cerr<<"rows "<<rows<<" alternating_cycles "<<j.cycles<<" reconnects "<<j.orders<<" unique "<<j.novel<<" skips "<<r.skips<<" best "<<r.best<<" parity_consistent "<<r.feasible<<"\n";
}
