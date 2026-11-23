// Walk among 96-vertex parity sets; every claimed hit is tested by the exact verifier.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <random>
#include <set>
using Key=array<uint64_t,4>;
void flip(Key& key,int x){key[x>>7]^=uint64_t(1)<<((x>>1)&63);}
int defect(const Search& s){
    array<int,512> capacity{};
    int leaves=0;
    for(int w=0;w<512;w++){
        int m=s.axes[w];
        if(popcount(unsigned(m))>2)continue;
        leaves+=has_single_bit(unsigned(m));
        while(m){int d=countr_zero(unsigned(m));m&=m-1;capacity[w^(1<<d)]++;}
    }
    int missing=max(0,2-leaves);
    for(int x:s.fixed)missing+=max(0,2-capacity[x]);
    return missing;
}
int main(int argc,char**argv){
    const int rounds=argc>1?atoi(argv[1]):20;
    mt19937_64 rng(argc>2?strtoull(argv[2],nullptr,10):1447);
    uint64_t steps=0,new_sets=0,exact=0,incomplete=0,distant=0;
    int farthest=0;
    vector<int> p(192);
    while(cin>>p[0]){
        for(int i=1;i<192;i++)if(!(cin>>p[i]))return 2;
        for(int i=0;i<192;i++){
            if(p[i]<0||p[i]>=512)return 3;
            for(int j=0;j<i;j++){
                int d=popcount(unsigned(p[i]^p[j]));if(!d||(d==1)!=(i==j+1))return 4;
            }
        }
        for(int side=0;side<2;side++){
            vector<int>a;array<bool,512> original{};Key key{};
            for(int i=side;i<192;i+=2){int x=p[i];a.push_back(x);original[x]=true;flip(key,x);}
            Search s(a,30000);
            set<Key> inspected{key},walked{key};
            int distance=0;
            for(int t=0;t<rounds;t++){
                int best=-1,choice_i=-1,choice_y=-1;
                for(int i=0;i<96;i++){
                    int old=s.fixed[i];s.toggle(old,i,false);
                    for(int index=0;index<256;index++){
                        int y=2*index;
                        y|=popcount(unsigned(y^old))&1;
                        if(y!=old && s.slot[y]<0){
                            int avail=0;
                            for(int d=0;d<9;d++)avail+=popcount(unsigned(s.axes[y^(1<<d)]))<=1;
                            if(avail>=1){
                                Key k=key;flip(k,old);flip(k,y);
                                if(!walked.contains(k)){
                                    s.fixed[i]=y;s.toggle(y,i,true);
                                    int miss=defect(s);
                                    int dist=distance+int(original[old])-int(original[y]);
                                    if(inspected.insert(k).second){
                                        new_sets++;
                                        if(miss==0){
                                            exact++;distant+=dist>=3;
                                            farthest=max(farthest,dist);
                                            if(s.test())return 0;
                                        }
                                    }
                                    if(miss<=1){
                                        int value=400*int(miss==0)+100*dist+int(rng()%1300);
                                        if(value>best){best=value;choice_i=i;choice_y=y;}
                                    }
                                    s.toggle(y,i,false);s.fixed[i]=old;
                                }
                            }
                        }
                    }
                    s.toggle(old,i,true);
                }
                if(choice_i<0)break;
                int old=s.fixed[choice_i];
                distance+=int(original[old])-int(original[choice_y]);
                s.toggle(old,choice_i,false);s.fixed[choice_i]=choice_y;s.toggle(choice_y,choice_i,true);
                flip(key,old);flip(key,choice_y);walked.insert(key);steps++;
            }
            incomplete+=s.unknown;
        }
    }
    cout<<"moves "<<steps<<" inspected "<<new_sets<<" tested zero-defect "<<exact
        <<" tested at distance >=3 "<<distant<<" maximum tested distance "<<farthest
        <<" unresolved "<<incomplete<<"\n";
}
