#define Q9_MIXED_CHECK
#include "q9_mixed_halves.cpp"
// Independent flat 9! x 512 replay for the first several nonempty placement rows.
set<Path> brute(const Path& a,const Path& b){
    array<int,512> forbidden{},nb{};
    for(int x:a){forbidden[x]=1;for(int d=0;d<9;d++)nb[x^(1<<d)]++;}
    array<int,9> perm{0,1,2,3,4,5,6,7,8};
    set<Path> poses;
    do{
        Path moved{0};
        for(size_t i=1;i<b.size();i++)moved.push_back(moved.back()^(1<<perm[countr_zero(unsigned(b[i]^b[i-1]))]));
        for(int t=0;t<512;t++){
            bool feasible=true;int edges=0;
            for(size_t j=0;j<moved.size();j++){
                int y=moved[j]^t;
                if(forbidden[y]){feasible=false;break;}
                if(!nb[y])continue;
                edges+=nb[y];
                if(edges!=1||(j>0&&j+1<moved.size())||(!JoinSearch::adjacent(y,a.front())&&!JoinSearch::adjacent(y,a.back()))){feasible=false;break;}
            }
            if(feasible){Path out;for(int x:moved)out.push_back(x^t);poses.insert(out);}
        }
    }while(next_permutation(perm.begin(),perm.end()));
    return poses;
}
int main(){
    ifstream mothers("q8_catalogue_96_98.words"),snakes("q9_far189_spring_20261121/comparison191.words");string w;set<string>a,b;
    while(mothers>>w)a.insert(canonical(w));while(snakes>>w){b.insert(canonical(w.substr(0,68)));b.insert(canonical(w.substr(w.size()-68)));}
    vector<Shape> donors;for(auto&s:b)donors.emplace_back(decodeWord(s),9);
    int positives=0,zeros=0;
    for(auto& s:a){
        Embed checker(9,192);checker.census=true;checker.setFirst(decodeWord(s));
        for(const auto& q:donors){
            checker.censusPaths.clear();checker.run(q);
            bool hit=!checker.censusPaths.empty();
            if(!hit&&zeros>=2)continue;
            auto actual=brute(checker.fixed,q.p);
            if(actual!=checker.censusPaths)throw runtime_error("9D replay differs");
            if(hit)positives++;else zeros++;
            cout<<"MATCH "<<actual.size()<<" "<<positives<<" "<<zeros<<endl;
            if(positives>=3&&zeros>=2){cout<<"DONE"<<endl;return 0;}
        }
    }
}
