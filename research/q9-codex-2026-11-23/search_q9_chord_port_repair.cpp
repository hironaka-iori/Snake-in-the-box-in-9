// Remove neighborhoods covering all chords before matching the exposed ports.
#define PORTS_LIBRARY
#include "search_q9_port_matching.cpp"
struct Defect{Path p;vector<pair<int,int>> chords;};
int main(int argc,char**argv){
    if(argc!=7 && argc!=8)return 2;bool exact=argc==8 && string(argv[7])=="exact";
    int trials=stoi(argv[1]),maxChord=stoi(argv[2]),radius=stoi(argv[3]),other=stoi(argv[4]),target=stoi(argv[5]);mt19937 rng(stoi(argv[6]));
    vector<Defect> bank;string w;int reported;
    while(cin>>reported>>w){if(reported>maxChord)continue;Defect d;d.p={0};for(char c:w)d.p.push_back(d.p.back()^(1<<(c-'0')));
        set<int> uniq(d.p.begin(),d.p.end());if(uniq.size()!=d.p.size())return 3;
        for(int i=0;i<d.p.size();i++)for(int j=i+2;j<d.p.size();j++)
            if(distanceQ(d.p[i],d.p[j])==1)d.chords.push_back({i,j});
        if(d.chords.size()!=reported)return 3;bank.push_back(std::move(d));
    }
    if(bank.empty())return 2;uint64_t nodes=0,cuts=0,part=0;
    vector<set<vector<pair<int,int>>>> visited(bank.size());uint64_t duplicates=0;
    int base=2*(radius+1)*(radius+1);
    if(exact){for(auto& b:bank)if(b.chords.size()!=2)return 2;trials=bank.size()*base*base;}
    for(int t=0;t<trials;t++){
        int id=t%bank.size();auto& d=bank[id];int n=d.p.size();vector<bool> free(n);
        auto drop=[&](int x,int a,int b){for(int j=max(0,x-a);j<=min(n-1,x+b);j++)free[j]=true;};
        int digit=t/bank.size();
        for(auto [a,b]:d.chords){
            if(exact){int option=digit%base;digit/=base;int which=option%2;option/=2;
                drop(which?a:b,option%(radius+1),option/(radius+1));}
            else drop((rng()&1)?a:b,rng()%(radius+1),rng()%(radius+1));
        }
        int more=exact?0:rng()%(other+1);
        for(int k=0;k<more;k++)drop(rng()%n,rng()%(radius+1),rng()%(radius+1));
        vector<pair<int,int>> pieces;
        for(int i=0;i<n;){if(free[i]){i++;continue;}int j=i;while(j+1<n&&!free[j+1])j++;
            if(j>i)pieces.push_back({i,j});i=j+1;}
        if(pieces.empty())continue;
        if(exact&&!visited[id].insert(pieces).second){duplicates++;continue;}
        Ports g;bool found=exact?g.run(d.p,pieces,target,12,10,150000,6000):g.run(d.p,pieces,target,5+rng()%5,3+rng()%5,7000,300);
        nodes+=g.nodes;cuts+=g.cutoff;part+=g.incomplete;
        if(found){cout<<"FOUND "<<id<<" "<<t;for(int v:g.witness)cout<<" "<<v;cout<<endl;return 0;}
        if((t+1)%5000==0||t+1==trials)cout<<"AT "<<t+1<<" "<<nodes<<" "<<cuts<<" "<<part<<endl;
    }
    cout<<"DONE "<<trials<<" "<<duplicates<<" "<<nodes<<" "<<cuts<<" "<<part<<endl;
}
