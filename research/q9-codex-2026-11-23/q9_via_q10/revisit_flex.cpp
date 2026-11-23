#define DETOUR_LIBRARY
#include "free_outer_tips.cpp"
#include "parity_bridge.inc"
int main(int argc,char** argv){
    if(argc!=5)return 2;
    ifstream words(argv[1]),in(argv[2]);string w,line;
    vector<Path> arms;while(words>>w)arms.push_back(vertices(w));
    mt19937 rng(stoul(argv[3]));int repeats=stoi(argv[4]),best=0;
    uint64_t placements=0,trials=0,consistent=0,joined=0,cap=0;
    while(getline(in,line)){
        istringstream row(line);string kind;row>>kind;if(kind!="PLACE")continue;
        placements++;int id,x;row>>id;Path b;while(row>>x)b.push_back(x);
        for(int i=0;i<repeats;i++){
            trials++;Path a=arms.at(id),r=b;
            if(i&1)reverse(a.begin(),a.end());if(i&2)reverse(r.begin(),r.end());
            int parity=(i/4)%2;
            int trim=i<8?0:rng()%6,cut=i<8?0:rng()%5;
            int l=trim+((popcount(unsigned(a[trim]))&1)!=parity);
            trim=i<8?0:rng()%6;
            int h=trim+((popcount(unsigned(r[trim]))&1)!=parity);
            FlexBridge s;
            for(int j=l;j<int(a.size())-cut;j+=2)s.left.push_back(a[j]);
            reverse(s.left.begin(),s.left.end());
            cut=i<8?0:rng()%5;
            for(int j=h;j<int(r.size())-cut;j+=2)s.right.push_back(r[j]);
            if(!s.init())continue;
            consistent++;s.limit=2000;
            s.join(6+rng()%8);
            joined+=!s.best.empty();cap+=s.visits>=s.limit;
            if(int(s.best.size())-1>best){
                best=s.best.size()-1;assert(valid(s.best));cout<<"BEST "<<best;
                for(int v:s.best)cout<<" "<<v;cout<<endl;
                if(best>=192)return 0;
            }
        }
        if(placements%500==0)cout<<"AT "<<placements<<" "<<joined<<" "<<best<<endl;
    }
    cout<<"DONE "<<placements<<" "<<trials<<" "<<consistent<<" "<<joined<<" "<<cap<<" "<<best<<endl;
}
