// Lift pairs in opposite Q8 layers with at least one induced cycle as parent.
#define main path_bank_main
#include "search_q8_multicross_bank.cpp"
#undef main
struct Parent {Path p; bool cyclic;};
bool valid_cycle(const Path& p){
    if(p.size()<4 || p.size()%2)return false;
    for(int i=0;i<int(p.size());i++)for(int j=0;j<i;j++){
        int dist=popcount(unsigned(p[i]^p[j]));
        if(!dist || (dist==1)!=(i==j+1||(j==0&&i+1==p.size())))return false;
    }
    return true;
}
int main(int argc,char**argv){
    if(argc!=6)return 2;
    int target=stoi(argv[1]),extra=stoi(argv[2]),minimum=stoi(argv[3]);
    vector<Parent> bank;set<string> seen;
    for(int t=0;t<2;t++){
        ifstream in(argv[4+t]);if(!in)return 2;string s;
        while(in>>s){
            if(int(s.size())<minimum)continue;
            Path p{0};for(char c:s){if(c<'0'||c>'7')return 3;p.push_back(p.back()^(1<<(c-'0')));}
            if(t==0){
                if(p.back()!=0)return 3;
                p.pop_back();if(!valid_cycle(p))return 3;
            }else{
                if(!valid(p,8))return 3;
                if(!seen.insert(min(word(p,false),word(p,true))).second)continue;
            }
            bank.push_back({p,!t});
        }
    }
    uint64_t pairs=0,placements=0,eligible=0,nodes=0;
    for(int i=0;i<int(bank.size());i++){
        if(!bank[i].cyclic)break;
        const auto& a=bank[i].p;array<Mask,256> lower{};
        for(int t=0;t<256;t++)for(int v:a){int x=v^t;lower[t][x/64]|=1ull<<(x%64);}
        for(int j=i;j<int(bank.size());j++){
            const auto& b=bank[j].p;int k=int(a.size()+b.size())+extra-(target+1);
            if(k<1+int(bank[j].cyclic))continue;
            array<int,8> perm{0,1,2,3,4,5,6,7};++pairs;
            do{
                int x=0;Mask m{};m[0]=1;Path upper{0};
                for(int h=1;h<int(b.size());h++){
                    x^=1<<perm[countr_zero(unsigned(b[h]^b[h-1]))];
                    upper.push_back(x);m[x/64]|=1ull<<(x%64);
                }
                placements+=256;
                for(int t=0;t<256;t++){
                    int overlap=0;
                    for(int d=0;d<4;d++)overlap+=popcount(m[d]&lower[t][d]);
                    if((!extra&&!overlap)||overlap>2*k+1)continue;
                    ++eligible;Refill r;r.goal=target;r.vertices=a;
                    for(int v:upper)r.vertices.push_back(256+(v^t));
                    for(int v:r.vertices)r.used[v]=true;
                    Path result=extra?r.refill_external(k,extra):r.visit(k);
                    nodes+=r.nodes;
                    if(!result.empty()){
                        if(!valid(result,9))return 4;
                        cout<<"FOUND "<<i<<" "<<j;for(int v:result)cout<<" "<<v;cout<<endl;return 0;
                    }
                }
            }while(next_permutation(perm.begin(),perm.end()));
        }
    }
    cout<<"NO_JOIN pairs "<<pairs<<" placements "<<placements<<" eligible "<<eligible<<" nodes "<<nodes<<endl;
}
