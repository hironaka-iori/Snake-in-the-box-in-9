#define Q9_TREE_LIBRARY
#include "tree.cpp"
int maxEven=97, keepCap=0;
struct Rem{
    const Donor& u;const Tree& t;int r;bool allowNew;
    array<uint8_t,256> load{},alive{};int total;
    uint64_t sets=0,finals=0,unknown=0;
    Rem(const Donor& d,const Tree& tr,int k,int pairs,bool add):u(d),t(tr),r(k),allowNew(add),total(pairs){
        alive=u.in;for(int x:u.p)for(int s:t.off)load[x^s]++;
    }
    void step(int x,int dir){alive[x]=dir>0;for(int s:t.off){int y=x^s;total-=load[y]==2;load[y]+=dir;total+=load[y]==2;}}
    bool dfs(int start,int left){
        int kept=int(u.p.size())-r,added=allowNew?maxEven-kept:0;
        if(added<0||(!allowNew&&kept<96))return false;
        int needed=kept-added-1;
        if(total+9*left<needed)return false;
        if(left){
            int counts[10]{};
            for(int j=start;j<int(u.p.size());j++){
                int x=u.p[j],score=0;for(int s:t.off){int d=load[x^s];score+=3<=d&&d<=2+left;}counts[score]++;
            }
            int bound=total,remain=left;
            for(int v=9;v&&remain;v--){int k=min(remain,counts[v]);bound+=v*k;remain-=k;}
            if(bound<needed)return false;
            for(int j=start;j+left<=int(u.p.size());j++){int x=u.p[j];step(x,-1);if(dfs(j+1,left-1))return true;step(x,1);}
            return false;
        }
        sets++;Path h;
        int deficit=0;
        for(int x:u.p)if(alive[x]){
            int ports=0;
            for(int s:t.off)ports+=load[x^s]==2;
            deficit+=max(0,2-ports);if(deficit>2*added+2)return false;
            h.push_back(image(x,t));
        }
        // Deleting all new even vertices from a Hamiltonian order leaves at most added+1 segments.
        array<uint8_t,256> visited{};int components=0;
        for(int x:u.p)if(alive[x]&&!visited[x]){
            if(++components>added+1)return false;
            Path q{x};visited[x]=1;
            for(size_t i=0;i<q.size();i++)for(int s:t.off){
                int y=q[i]^s;if(load[y]!=2)continue;
                for(int z:t.off){int v=y^z;if(alive[v]&&!visited[v]){visited[v]=1;q.push_back(v);}}
            }
        }
        finals++;
        if(keepCap){
            if(finals<=uint64_t(keepCap)){cout<<"KEEP "<<kept;for(int q:h)cout<<" "<<q;cout<<endl;}
            return false;
        }
        if(!allowNew || added==0){
            Search e(h,1000000,h.size()>=97);if(e.test())return true;unknown+=e.unknown;return false;
        }
        // With precisely 96 retained vertices, both endpoint-color possibilities
        // require either no additional even vertex, or a single additional even vertex.
        auto fill=[&](auto&& self,int start)->bool{
            int size=int(h.size());
            if(size==96||size==97){
                Search ask(h,1000000,size==97);
                if(ask.test())return true;unknown+=ask.unknown;
            }
            if(size==97)return false;
            for(int x=start;x<256;x++)if(!u.in[x]){
                h.push_back(image(x,t));
                if(self(self,x+1))return true;
                h.pop_back();
            }
            return false;
        };
        return fill(fill,0);
    }
};
#ifndef Q9_REM_LIBRARY
int main(int argc,char**argv){
 if(argc!=5 && argc!=7)return 2;if(argc==7){maxEven=stoi(argv[5]);keepCap=stoi(argv[6]);}int from=stoi(argv[1]),to=stoi(argv[2]),add=stoi(argv[3]),kept=stoi(argv[4]);
 Edges base{};base[0]={0,1};base[1]={1,2};grow(base,3);string w;int row=-1;
 while(cin>>w){++row;if(row<from||row>=to)continue;Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));Donor u(p);
    int k=int(p.size())-kept;if(k<0)continue;uint64_t pre=0,checked=0,finals=0,unk=0;
    for(int j=0;j<int(trees.size());j++){
        const auto& t=trees[j];int e=u.pairs(t);if(e+9*k<kept-(add?maxEven-kept:0)-1)continue;pre++;Rem r(u,t,k,e,add);
        if(r.dfs(0,k)){cout<<"SOURCE "<<row<<" "<<j<<endl;return 0;}checked+=r.sets;finals+=r.finals;unk+=r.unknown;
    }
    cout<<"ROW "<<row<<" "<<trees.size()<<" "<<k<<" "<<pre<<" "<<checked<<" "<<finals<<" "<<unk<<endl;
 }
}

#endif
