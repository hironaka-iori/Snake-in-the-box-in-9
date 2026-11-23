// Enumerate mixed parity halves, apply monotone local bounds, then test a Hamiltonian path.
#define main unused_combinations_driver
#include "../search_q9_parity_combinations.cpp"
#undef main
#include <random>
struct Region{
    int n, cap, hcap;bool major,cut=false;
    Bounds state;vector<int> base,pool;
    long long nodes=0,leaves=0,graphs=0,hu=0,low=0,dead=0;
    bool choose(int need,const vector<int>& options){
        if(++nodes>cap){cut=true;return false;}
        if(state.poor>(major?2:0))return false;
        if(!need){
            leaves++;
            if(state.counts[2]<n-1||(!major&&state.counts[1]<2))return false;
            vector<int> picked;
            for(int v=0;v<512;v++)if(state.occupied[v])picked.push_back(v);
            if(int(picked.size())!=n)abort();
            graphs++;Search s(picked,hcap,major);if(s.test())return true;
            hu+=s.unknown;low+=s.low;dead+=s.dead;return false;
        }
        vector<int> viable;
        for(int x:options){
            if(state.room[x]<(major?1:2))continue;
            state.change(x,1);if(state.poor<=(major?2:0))viable.push_back(x);
            state.change(x,-1);
        }
        for(int i=0;i+need<=viable.size();i++){
            int x=viable[i];state.change(x,1);
            if(choose(need-1,vector<int>(viable.begin()+i+1,viable.end())))return true;
            state.change(x,-1);if(cut)return false;
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;
    int cap=stoi(argv[1]),release=stoi(argv[2]),goal=stoi(argv[3]),row=0;
    mt19937 rng(stoul(argv[4]));int n,nc,nf;
    while(cin>>n>>nc>>nf){
        vector<int> base(nc),pool(nf);for(int &v:base)cin>>v;for(int &v:pool)cin>>v;
        bool major=(n==goal/2+1);if(!major&&n!=goal/2)return 3;
        Bounds full;for(int x:base)full.change(x,1);
        vector<int> order=base;shuffle(order.begin(),order.end(),rng);
        stable_sort(order.begin(),order.end(),[&](int x,int y){return full.room[x]<full.room[y];});
        for(int r=0;r<(release?min(release,nc):1);r++){
            Region s{n,cap,120000,major};s.state=full;vector<int> options=pool;shuffle(options.begin(),options.end(),rng);
            int omit=-1;
            if(release){omit=order[r];s.state.change(omit,-1);}
            bool found=s.choose(n-nc+int(release>0),options);
            cout<<"ROW "<<row<<" "<<omit<<" "<<s.nodes<<" "<<s.leaves<<" "<<s.graphs<<" "<<s.low<<" "<<s.dead<<" "<<s.hu<<" "<<s.cut<<" "<<found<<endl;
            if(found)return 0;
        }
        row++;
    }
}
