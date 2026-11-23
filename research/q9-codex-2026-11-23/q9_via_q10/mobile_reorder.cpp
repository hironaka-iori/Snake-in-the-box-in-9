#define Q9_PARITY_LIBRARY
#include "../search_q9_fixed_parity.cpp"
#include <algorithm>
#include <fstream>
#include <random>
#include <set>
#include <sstream>
int main(int argc,char**argv){
    if(argc<3)return 2;
    int mutation=stoi(argv[1]);set<vector<int>> seen;vector<pair<vector<int>,bool>> sets;
    for(int arg=2;arg<argc;arg++){
        ifstream input(argv[arg]);string line;
        while(getline(input,line)){
            istringstream row(line);vector<int> p;int x;while(row>>x)p.push_back(x);
            for(int start=0;start+192<int(p.size());start++)for(int side:{0,1}){
                vector<int> s;for(int j=start+side;j<=start+192;j+=2)s.push_back(p[j]);
                sort(s.begin(),s.end());if(adjacent_find(s.begin(),s.end())!=s.end())continue;
                if(seen.insert(s).second)sets.push_back({s,side==0});
            }
        }
    }
    mt19937 rng(641955);shuffle(sets.begin(),sets.end(),rng);
    uint64_t base=0,total=0,low=0,dead=0,unknown=0;
    for(auto& [fix,maj]:sets){
        Search s(fix,75000,maj);if(s.test())return 0;int n=fix.size();
        if(mutation){
            vector<int> out;
            for(int v=0;v<512;v++)if(s.slot[v]<0 && popcount(unsigned(v^fix[0]))%2==0)out.push_back(v);
            vector<int> order(n);iota(order.begin(),order.end(),0);shuffle(order.begin(),order.end(),rng);
            for(int i:order){
                int old=fix[i];s.toggle(old,i,false);
                for(int extra:out){
                    int useful=0;for(int b=1;b<512;b*=2){
                        int m=s.axes[extra^b],d=popcount(unsigned(m));
                        if(d==1 || (!maj && d==0))useful++;
                    }
                    if(useful<(maj?1:2))continue;
                    s.toggle(extra,i,true);s.fixed[i]=extra;if(s.test())return 0;s.toggle(extra,i,false);
                }
                s.fixed[i]=old;s.toggle(old,i,true);
            }
        }
        total+=s.tested;low+=s.low;dead+=s.dead;unknown+=s.unknown;base++;
        if(base%250==0)cout<<"AT "<<base<<" "<<sets.size()<<" "<<total<<" "<<low<<" "<<dead<<" "<<unknown<<endl;
    }
    cout<<"DONE "<<base<<" "<<total<<" "<<low<<" "<<dead<<" "<<unknown<<endl;
}
