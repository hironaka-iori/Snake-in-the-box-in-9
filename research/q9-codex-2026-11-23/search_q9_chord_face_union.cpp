// Free disjoint cube faces touching a chord and refill their union at fixed total size.
#define main previous_search_main
#include "search_q9_parity_regions.cpp"
#undef main
#include <set>
int main(int argc,char** argv){
    if(argc!=6 && argc!=7)return 2;
    int shears=argc==7?stoi(argv[6]):0;
    int rounds=stoi(argv[1]),seed=stoi(argv[2]),ndim=stoi(argv[3]),cells=stoi(argv[4]),cap=stoi(argv[5]);
    if(ndim<2||ndim>7||cells<1||cells>(1<<(9-ndim))||rounds<1||cap<1)return 2;
    vector<vector<int>> walks;vector<vector<int>> anchors;string l;
    while(getline(cin,l)){
        istringstream in(l);vector<int> p,hot;int v;
        while(in>>v){if(v<0||v>=512)return 3;p.push_back(v);}
        if(p.size()<5||p.size()%2==0||set<int>(p.begin(),p.end()).size()!=p.size())return 3;
        for(int j=0;j<p.size();j++)for(int i=0;i<j;i++){
            if(popcount(unsigned(p[i]^p[j]))!=1){if(i+1==j)return 3;continue;}
            if(i+1!=j){hot.push_back(p[i]);hot.push_back(p[j]);}
        }
        walks.push_back(p);anchors.push_back(hot);
    }
    mt19937 rng(seed);uint64_t done=0,cut=0,nodes=0,graph=0,unknown=0,hard=0;
    for(int k=0;k<rounds;k++){
        auto idx=rng()%walks.size();const auto& p=walks[idx];const auto& hot=anchors[idx];
        vector<int> axes{0,1,2,3,4,5,6,7,8};shuffle(axes.begin(),axes.end(),rng);
        int fixed=511;for(int i=0;i<ndim;i++)fixed^=1<<axes[i];
        array<int,512> encoded;
        for(int v=0;v<512;v++)encoded[v]=v;
        // Each shear is invertible and preserves parity. Apply only to cell labels.
        for(int j=0;j<shears;j++){
            array<int,9> perm{0,1,2,3,4,5,6,7,8};shuffle(perm.begin(),perm.end(),rng);
            int toggle=(1<<perm[1])|(1<<perm[2]);
            for(int& v:encoded)if(v & (1<<perm[0]))v^=toggle;
        }
        vector<int> boxes;
        auto insert=[&](int v){v&=fixed;if(find(boxes.begin(),boxes.end(),v)==boxes.end())boxes.push_back(v);};
        insert(encoded[hot.empty()?p[rng()%p.size()]:hot[rng()%hot.size()]]);
        for(int i=0;boxes.size()<cells;i++){
            int v=encoded[p[rng()%p.size()]];
            if(k%3==0&&i<30)v=boxes[rng()%boxes.size()]^(1<<axes[ndim+rng()%(9-ndim)]);
            if(k%3==1&&i<30&&!hot.empty()){v=encoded[hot[rng()%hot.size()]];for(int j=0;j<2;j++)v^=1<<axes[rng()%9];}
            if(i>50)v=rng()%512;
            insert(v);
        }
        auto mutable_v=[&](int v){return find(boxes.begin(),boxes.end(),encoded[v]&fixed)!=boxes.end();};
        Region search;search.cap=cap;search.needed=p.size()/2;
        int released=0;
        for(int j=1;j<p.size();j+=2){if(mutable_v(p[j]))released++;else search.state.change(p[j],1);}
        hard+=released>=5;bool hit=false;
        if(!search.state.poor){
            vector<int> pool;for(int v=0;v<512;v++)if(mutable_v(v)&&!__builtin_parity(unsigned(v^p[1])))pool.push_back(v);
            shuffle(pool.begin(),pool.end(),rng);hit=search.fill(pool,released);
        }
        nodes+=search.visits;cut+=search.limited;graph+=search.exact;unknown+=search.unknown;done++;
        if(hit||done%2500==0||done==rounds){
            cout<<(hit?"HIT":"STATS")<<" "<<done<<" "<<hard<<" "<<nodes<<" "<<graph<<" "<<cut<<" "<<unknown<<endl;
            if(hit)return 0;
        }
    }
}
