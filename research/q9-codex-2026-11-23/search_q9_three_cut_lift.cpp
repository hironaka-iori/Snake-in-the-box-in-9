// Recombine four projected path fragments in all orders around three cuts.
// For each resulting projection, reuse the exact binary layer recoloring DP.
#define main recolor_entry_point
#include "search_q9_recolor_projection.cpp"
#undef main
#include <unordered_set>
struct Rejoin {
    Run &solver;
    int gap;
    long long triples=0, orders=0, novel=0;
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
        // Removing three old edges in a pure 3-opt move, and holding the two
        // global ends, creates three links whose matching on the six freed
        // endpoints forms an alternating 6-cycle with the three old edges.
        std::set<std::array<int,3>> cuts;
        for(int i=0;i+1<n;++i)for(int side:{0,1}){
            int a=i+side;
            for(int w:contact[a])for(int j:{w,w-1}){
                if(j<0||j+1>=n||abs(i-j)<gap)continue;
                int b=j+(j+1-w);
                for(int y:contact[b])for(int k:{y,y-1}){
                    if(k<0||k+1>=n||abs(k-i)<gap||abs(k-j)<gap)continue;
                    int c=k+(k+1-y);
                    if(__builtin_popcount(unsigned(p[c]^p[i+1-side]))!=1)continue;
                    std::array<int,3> q{i,j,k};std::sort(q.begin(),q.end());cuts.insert(q);
                }
            }
        }
        triples+=cuts.size();
        for(auto t:cuts){
            int i=t[0],j=t[1],k=t[2];
            for(int perm:{0,1})for(int rev1:{0,1})for(int rev2:{0,1}){
                int lo[2]={i+1,j+1},hi[2]={j,k}, idx=perm,idx2=1-perm;
                int a=rev1?hi[idx]:lo[idx],b=rev1?lo[idx]:hi[idx];
                int c=rev2?hi[idx2]:lo[idx2],d=rev2?lo[idx2]:hi[idx2];
                auto adjacent=[&](int x,int y){return abs(x-y)>1 && __builtin_popcount(unsigned(p[x]^p[y]))==1;};
                if(!adjacent(i,a)||!adjacent(b,c)||!adjacent(d,k+1))continue;
                P result(p.begin(),p.begin()+i+1);
                auto append=[&](int x,int y){for(int v=x;;v+=x<y?1:-1){result.push_back(p[v]);if(v==y)return;}};
                append(a,b);append(c,d);result.insert(result.end(),p.begin()+k+1,p.end());orders++;
                if(unique.insert(signature(result)).second){solver.eval(result);novel++;}
            }
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
    std::cerr<<"rows "<<rows<<" candidate_cut_triples "<<j.triples<<" reconnects "<<j.orders<<" unique "<<j.novel<<" skips "<<r.skips<<" best "<<r.best<<" parity_consistent "<<r.feasible<<"\n";
}
