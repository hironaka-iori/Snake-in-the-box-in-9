// Use two Q8 record fragments, in opposite Q9 layers. Pack their projected
// positions, release three axes, and reconnect and extend in all nine axes.
#define Q9_VARIABLE_FOREST_LIBRARY
#include "search_q9_variable_projected_forest.cpp"
struct Stats8{Stats st;uint64_t layouts=0,arr=0;};
bool place(Path a,Path b,int phase,int mask,int goal,int cc,int bc,Stats8& tally){
    Path keep=a,times;int n=a.size();keep.insert(keep.end(),b.begin(),b.end());
    for(int i=0;i<keep.size();i++)times.push_back(i+(i<n?0:1+phase));
    tally.layouts++;return enumerateColors(keep,times,mask,cc,tally.st,[&](const Path& colored){
        vector<Path> parts{{colored.begin(),colored.begin()+n},{colored.begin()+n,colored.end()}};
        for(int flips=0;flips<4;flips++){
            auto pair=parts;for(int i=0;i<2;i++)if(flips&(1<<i))reverse(pair[i].begin(),pair[i].end());
            Join join(std::move(pair),goal,bc);tally.arr++;bool hit=join.next(0);tally.st.bridgeLimits+=join.cutoff;tally.st.bridgeNodes+=join.nodes;
            if(hit){cout<<"FOUND "<<join.result.size()-1;for(int x:join.result)cout<<" "<<x;cout<<endl;return true;}
        }
        return false;
    });
}
void verify8(const Path& p){
 for(int i=0;i<p.size();i++){assert(p[i]>=0&&p[i]<256);for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));assert(d>0&&((d==1)==(j+1==i)));}}
}
int main(int argc,char**argv){
    if(argc!=5)return 2;int trials=stoi(argv[1]),cc=stoi(argv[2]),bc=stoi(argv[3]);mt19937 rng(stoi(argv[4]));
    vector<Path> bank;string w;while(cin>>w){Path p{0};for(char c:w){assert(c>='0'&&c<='7');p.push_back(p.back()^(1<<(c-'0')));}verify8(p);bank.push_back(p);}
    Stats8 tally;
    if(!trials){
        auto p=bank[0];int k=p.size()/2;
        Path a(p.begin(),p.begin()+k),b(p.begin()+k+2,p.end());for(int& x:b)x^=256;
        for(int phase=0;phase<2;phase++)if(place(a,b,phase,7,p.size(),cc,bc,tally))return 0;
        return 4;
    }
    Path masks;for(int m=1;m<512;m++)if(popcount(unsigned(m))==3)masks.push_back(m);
    for(int i=0;i<trials;i++){
        auto choose=[&](){
            Path p=bank[rng()%bank.size()];if(rng()%2)reverse(p.begin(),p.end());
            int trim=rng()%20,lo=rng()%(trim+1);return Path(p.begin()+lo,p.end()-trim+lo);
        };
        auto a=choose(),b=choose();array<int,8> perm;iota(perm.begin(),perm.end(),0);
        if(rng()%3)shuffle(perm.begin(),perm.end(),rng);else swap(perm[rng()%8],perm[rng()%8]);
        for(int& x:b){int y=0;for(int t=0;t<8;t++)if(x&(1<<t))y|=1<<perm[t];x=y;}
        array<int,256> overlap{};for(int x:a)for(int y:b)overlap[x^y]++;
        array<pair<int,int>,256> rank;
        for(int z=0;z<256;z++)rank[z]={overlap[z]*1000+int(rng()%1000),z};
        int index=rng()%4;nth_element(rank.begin(),rank.begin()+index,rank.end());int shift=rank[index].second;
        for(int& x:b)x^=shift|256;
        int mask=masks[rng()%masks.size()];
        for(int phase=0;phase<2;phase++)if(place(a,b,phase,mask,192,cc,bc,tally))return 0;
        if((i+1)%10000==0)cout<<"AT "<<i+1<<" "<<tally.layouts<<" "<<tally.st.colorings<<" "<<tally.arr<<" "<<tally.st.colorLimits<<" "<<tally.st.bridgeLimits<<endl;
    }
    cout<<"DONE "<<trials<<" "<<tally.layouts<<" "<<tally.st.colorings<<" "<<tally.arr<<" "<<tally.st.colorLimits<<" "<<tally.st.bridgeLimits<<endl;
}
