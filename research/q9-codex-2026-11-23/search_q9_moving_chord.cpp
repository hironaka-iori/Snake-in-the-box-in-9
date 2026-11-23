#include "q9_excused_rethread.hpp"
int main(int argc,char**argv){
    if(argc!=3)return 2;
    ifstream input(argv[1]);ofstream out(argv[2]);if(!input||!out)return 2;
    set<string> known;string line;
    while(getline(input,line)){
        istringstream in(line);int v;Path p;while(in>>v)p.push_back(v);
        if(p.size()!=193)return 3;known.insert(encode(p));
    }
    set<Path> seen;string word;int row=0;
    while(cin>>word){
        if(word.size()!=192)return 3;
        Path p{0};for(char c:word){if(c<'0'||c>'8')return 3;p.push_back(p.back()^(1<<(c-'0')));}
        if(set<int>(p.begin(),p.end()).size()!=193)return 3;
        Repair r{0,0,100000,known,out};
        for(int side=0;side<2;side++){
            Path fixed;for(int i=side;i<p.size();i+=2)fixed.push_back(p[i]);
            sort(fixed.begin(),fixed.end());
            if(!seen.insert(fixed).second)continue;
            bool major=fixed.size()==97;
            Search s(fixed,100000);
            // If an exception is used, its opposite-color endpoint has original
            // load 3 (internal), or load 2 (terminal on the nonfixed side).
            for(int y=0;y<512;y++){
                unsigned mask=s.axes[y];int load=popcount(mask);
                if(load!=3 && (major||load!=2))continue;
                while(mask){
                    int x=y^(1<<countr_zero(mask));mask&=mask-1;
                    r.a=x;r.b=y;if(r.run(s))return 0;
                }
            }
        }
        cout<<"ROW "<<row++<<" "<<seen.size()<<" "<<r.tests<<" "<<r.graphs<<" "<<r.unknown<<" "<<r.positive<<" "<<r.lifts<<" "<<r.fresh<<endl;
    }
}
