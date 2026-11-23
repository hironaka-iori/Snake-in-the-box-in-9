#define Q9_PROJECTED_GAP_LIBRARY
#include "search_q9_free_projected_gaps.cpp"
// Independent oracle extends an explicit Q9 walk by single-bit flips. It sees
// only the specified six coordinates at the retained time indices.
int direct(const Path& base,int mask,const vector<Gap>& gaps){
    int n=base.size();Path fixed(n,1),p{base.front()&~mask};
    for(auto g:gaps)for(int i=g.first+1;i<g.last;i++)fixed[i]=0;
    uint64_t nodes=0;
    auto visit=[&](auto&& self)->int{
        int i=p.size();if(i==n)return 1;if(++nodes>2000000)return -1;
        for(int bit=1;bit<512;bit*=2){
            int v=p.back()^bit;if(fixed[i]&&((v^base[i])&~mask))continue;
            bool ok=true;for(int j=0;j+1<i;j++)if(popcount(unsigned(v^p[j]))<=1){ok=false;break;}
            if(!ok)continue;p.push_back(v);int r=self(self);p.pop_back();if(r!=0)return r;
        }
        return 0;
    };return visit(visit);
}
int main(){
    mt19937 rng(67349);int positive=0,negative=0,incomplete=0,two=0;
    for(int t=0;t<400;t++){
        int n=7+rng()%8;Path p{0};while(p.size()<n){int d=rng()%5;p.push_back(p.back()^(d<2?(1<<(3+d)):0));}
        int b=1+rng()%(n-3);vector<Gap> gaps{{b-1,b+1}};
        if(b+4<n&&rng()%2){gaps.push_back({b+2,b+4});two++;}
        Stats stats;Path result;bool found=search(p,7,gaps,100000,200000,stats,result);
        int oracle=direct(p,7,gaps);if(oracle<0){incomplete++;continue;}
        assert(!stats.bridgeLimits&&!stats.colorLimits&&found==bool(oracle));
        if(found)positive++;else negative++;
    }
    cout<<"CHECKED "<<positive+negative<<" matched_yes "<<positive<<" matched_no "<<negative<<" oracle_limit "<<incomplete<<" two_gap_inputs "<<two<<endl;
}
