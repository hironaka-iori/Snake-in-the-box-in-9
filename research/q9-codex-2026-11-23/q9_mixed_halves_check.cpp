#define Q9_MIXED_CHECK
#include "q9_mixed_halves.cpp"
#include <map>
#include <random>

void listPaths(Path& path,vector<Path>& rooted){
    rooted.push_back(path);
    for(int d=0;d<4;d++){
        int y=path.back()^(1<<d),contacts=0;
        for(int x:path){if(x==y){contacts=2;break;}contacts+=JoinSearch::adjacent(x,y);}
        if(contacts!=1)continue;
        path.push_back(y);listPaths(path,rooted);path.pop_back();
    }
}

int main(){
    vector<Path> paths;Path seed{0};listPaths(seed,paths);
    map<int,int> occupancies;
    for(const auto&p:paths)for(int t=0;t<16;t++){int mask=0;for(int x:p)mask|=1<<(x^t);occupancies[mask]=int(p.size());}
    vector<int> maxContaining(1<<16);
    for(auto [mask,n]:occupancies)maxContaining[mask]=n;
    for(int d=0;d<16;d++)for(int m=0;m<(1<<16);m++)if(!(m&(1<<d)))maxContaining[m]=max(maxContaining[m],maxContaining[m|(1<<d)]);
    mt19937 rnd(112103);uint64_t poses=0,positives=0,negatives=0;
    struct Quiet:streambuf{int overflow(int c)override{return c;}} quiet;
    auto old=cout.rdbuf(&quiet);
    for(int trial=0;trial<2000;trial++){
        Path a=paths[rnd()%paths.size()],b=paths[rnd()%paths.size()];
        if(a.size()<2||b.size()<2){trial--;continue;}
        int target=6+rnd()%3;
        set<Path> expected;int maskA=0;for(int x:a)maskA|=1<<x;bool exists=false;
        array<int,4> perm{0,1,2,3};
        do{
            Path imageB;
            for(int x:b){int v=0;for(int j=0;j<4;j++)if(x&(1<<j))v|=1<<perm[j];imageB.push_back(v);}
            for(int t=0;t<16;t++){
                Path m=imageB;int mb=0;for(int& x:m){x^=t;mb|=1<<x;}
                if(maskA&mb)continue;
                if(maxContaining[maskA|mb]>=target+1)exists=true;
                int contacts=0;bool atTips=false;for(int x:a)for(int y:m)if(JoinSearch::adjacent(x,y)){
                    contacts++;atTips|=(x==a.front()||x==a.back())&&(y==m.front()||y==m.back());
                }
                if(!contacts||(contacts==1&&atTips))expected.insert(m);
            }
        }while(next_permutation(perm.begin(),perm.end()));
        Shape shape(b,4);Embed census(4,target);census.setFirst(a);census.census=true;census.run(shape);
        if(expected!=census.censusPaths||expected.size()!=census.admitted)throw runtime_error("placement mismatch");
        Embed witness(4,target);witness.setFirst(a);
        if(witness.run(shape)!=exists)throw runtime_error("path mismatch");
        poses+=expected.size();positives+=exists;negatives+=!exists;
    }
    cout.rdbuf(old);cout<<"MATCH 2000 "<<poses<<" "<<positives<<" "<<negatives<<endl;
}
