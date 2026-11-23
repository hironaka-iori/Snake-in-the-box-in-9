// Rebuild the opposite colour freely. Force at least five minority vertices outside each source.
#define main earlier_regions
#include "../search_q9_parity_regions.cpp"
#undef main
#include <fstream>
struct Case{vector<int> a,b;};
int main(int argc,char**argv){
    if(argc!=5)return 2;
    ifstream in(argv[1]);string line;vector<Case> cases;
    while(getline(in,line)){
        istringstream row(line);vector<int> both;for(int x;row>>x;)both.push_back(x);
        if(both.size()!=380)return 3;
        for(int col=0;col<2;++col){
            Case next;
            for(int i=0;i<380;++i)if(__builtin_parity(unsigned(both[i]))==col)(i<190?next.a:next.b).push_back(both[i]);
            if(next.a.size()!=95||next.b.size()!=95)return 3;
            cases.push_back(move(next));
        }
    }
    int tries=stoi(argv[2]),cap=stoi(argv[3]);mt19937 rng(stoi(argv[4]));
    uint64_t built=0,nodes=0,terminal=0,unknown=0,truncated=0;
    for(int trial=0;trial<tries;++trial){
        auto& c=cases[rng()%cases.size()];bool flip=rng()&1;
        auto a=flip?c.b:c.a,b=flip?c.a:c.b;
        array<bool,512> ina{},inb{},locked{};
        for(int v:a)ina[v]=true;
        for(int v:b)inb[v]=true;
        vector<int> ai,bi;for(int v:b)if(!ina[v])bi.push_back(v);for(int v:a)if(!inb[v])ai.push_back(v);
        if(min(ai.size(),bi.size())<5)continue;
        shuffle(ai.begin(),ai.end(),rng);shuffle(bi.begin(),bi.end(),rng);
        for(int i=0;i<5;++i)locked[ai[i]]=true;
        Region search;search.cap=cap;
        for(int v:a)search.state.change(v,1);
        for(int j=0;j<5;++j)search.state.change(bi[j],1);
        int release=8+rng()%12;
        for(int j=0;j<release;++j){
            int best=-1000000,choice=-1;
            for(int v:a)if(!locked[v]&&search.state.occupied[v]){
                search.state.change(v,-1);
                int score=-100*search.state.poor+2*min(100,search.state.counts[2])+min(search.state.counts[1],8)+int(rng()%20);
                search.state.change(v,1);
                if(score>best){choice=v;best=score;}
            }
            if(choice<0)abort();
            search.state.change(choice,-1);
        }
        if(search.state.poor)continue;
        vector<int> possible;
        for(int v=0;v<512;++v){
            if(search.state.occupied[v]||__builtin_parity(unsigned(v^a.front())))continue;
            if(trial%3==0&&!ina[v]&&!inb[v])continue;
            possible.push_back(v);
        }
        shuffle(possible.begin(),possible.end(),rng);++built;
        if(search.fill(possible,release-4))return 0;
        nodes+=search.visits;terminal+=search.exact;unknown+=search.unknown;truncated+=search.limited;
        if(trial%100==0)cout<<"AT "<<trial<<" "<<built<<" "<<nodes<<" "<<terminal<<" "<<unknown<<" "<<truncated<<endl;
    }
    cout<<"DONE "<<tries<<" "<<built<<" "<<nodes<<" "<<terminal<<" "<<unknown<<" "<<truncated<<endl;
}
