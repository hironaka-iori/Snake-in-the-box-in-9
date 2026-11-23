// Pair independently sourced, oriented induced Q9 fragments whose edge lengths sum to 191.
#define main previous_pivot_driver
#include "../search_q9_pivot.cpp"
#undef main
#include <cassert>
#include <fstream>
#include <random>
#include <sstream>
#include <unordered_set>
using Path=vector<int>;using Profile=array<int,10>;
string canon(string s){array<int,9> rename;rename.fill(-1);int n=0;for(char& ch:s){int& a=rename[ch-'0'];if(a<0)a=n++;ch=char('0'+a);}return s;}
struct Shape{string w;Path p;Profile demand{};};
struct Host{int root;Profile supply{};array<bool,512> allowed{};};
Shape shape(const string& w){
    Shape s;s.w=w;s.p={0};for(char ch:w)s.p.push_back(s.p.back()^(1<<(ch-'0')));
    assert(valid(s.p));for(int v:s.p)s.demand[popcount(unsigned(v))]++;return s;
}
vector<Host> hosts(const Shape& s){
    array<int,512> occupied{},deg{};
    for(int x:s.p){occupied[x]=1;for(int d=1;d<512;d*=2)deg[x^d]++;}
    vector<Host> out;
    for(int d=1;d<512;d*=2){
        int t=s.p.back()^d;if(occupied[t]||deg[t]!=1)continue;
        Host h;h.root=t;Path q{t};h.allowed[0]=true;
        for(size_t i=0;i<q.size();i++){
            int v=q[i];h.supply[popcount(unsigned(v^t))]++;
            for(int b=1;b<512;b*=2){int y=v^b;if(!occupied[y]&&!deg[y]&&!h.allowed[y^t]){h.allowed[y^t]=true;q.push_back(y);}}
        }
        out.push_back(h);
    }return out;
}
struct Pattern{
    array<int,9> axes{};array<Path,9> ready;
    explicit Pattern(const Shape& b){
        int assigned=0;
        for(int j=0;j<9;j++){
            int best=-1,score=-1;
            for(int d=0;d<9;d++)if(!(assigned&(1<<d))){
                int n=0;for(int v:b.p)n+=!(v&~(assigned|(1<<d)));
                if(n>score){score=n;best=d;}
            }
            axes[j]=best;assigned|=1<<best;
            for(int v:b.p)if(!(v&~assigned)&&(v&(1<<best)))ready[j].push_back(v);
        }
    }
};
void windows(const Path& p,int n,unordered_set<string>& out){
    for(int lo=0;lo+n<int(p.size());lo++){
        string w;bool good=true;for(int i=lo;i<lo+n;i++){
            int v=p[i]^p[i+1];if(!has_single_bit(unsigned(v))){good=false;break;}w+=char('0'+countr_zero(unsigned(v)));
        }
        if(!good)continue;
        Path frag(p.begin()+lo,p.begin()+lo+n+1);if(!valid(frag))continue;
        out.insert(canon(w));reverse(w.begin(),w.end());out.insert(canon(w));
    }
}
#ifndef GROUP_CROSS_LIBRARY
int main(int argc,char**argv){
    if(argc!=6)return 2;int left=stoi(argv[1]),right=191-left,cap=stoi(argv[2]);mt19937 rng(stoul(argv[3]));bool control=stoi(argv[5]);if(control)right--;
    array<unordered_set<string>,2> known,fresh;string s;ifstream fp(argv[4]);
    while(fp>>s){
        auto a=shape(s);windows(a.p,left,known[0]);windows(a.p,right,known[1]);if(control)break;
    }
    while(getline(cin,s)){
        istringstream in(s);Path p;for(int v;in>>v;)p.push_back(v);
        windows(p,left,fresh[0]);windows(p,right,fresh[1]);
    }
    vector<Shape> arms[2];int original[2]{},novel[2]{};
    for(int side=0;side<2;side++){
        vector<string> a(fresh[side].begin(),fresh[side].end());sort(a.begin(),a.end());shuffle(a.begin(),a.end(),rng);
        for(const auto& w:a)if(!known[side].count(w)){novel[side]++;if(int(arms[side].size())<cap)arms[side].push_back(shape(w));}
        // Left fragment is outside the baseline bank. Right fragment may also be a baseline shape.
        if(side==1||control){
            vector<string> k(known[side].begin(),known[side].end());sort(k.begin(),k.end());shuffle(k.begin(),k.end(),rng);
            for(const auto& w:k){if(original[side]>=cap)break;arms[side].push_back(shape(w));original[side]++;}
        }
    }
    vector<Pattern> patterns;for(auto& b:arms[1])patterns.emplace_back(b);
    cout<<"BANK "<<left<<" "<<right<<" "<<novel[0]<<" "<<novel[1]<<" "<<arms[0].size()<<" "<<arms[1].size()<<endl;
    uint64_t tries=0,ports=0,passes=0,nodes=0;
    for(auto& a:arms[0]){auto hs=hosts(a);
        for(int j=0;j<int(arms[1].size());j++){auto& b=arms[1][j];tries++;
            for(const auto& h:hs){ports++;bool enough=true;for(int k=0;k<=9;k++)if(h.supply[k]<b.demand[k]){enough=false;break;}
                if(!enough)continue;
                Pivot t;for(int k=0;k<512;k++)t.bad[k]=!h.allowed[k];t.axes=patterns[j].axes;t.ready=patterns[j].ready;
                passes++;bool ok=t.visit(0,511);nodes+=t.nodes;
                if(ok){Path q=a.p;for(int x:b.p)q.push_back(h.root^t.mapped[x]);assert(valid(q)&&int(q.size())==left+right+2);
                    cout<<"FOUND";for(int x:q)cout<<" "<<x;cout<<endl;return 0;}
                assert(t.leaves==362880);
            }
        }
        if((&a-&arms[0][0])%100==0)cout<<"CHECK "<<tries<<" "<<ports<<" "<<passes<<" "<<nodes<<endl;
    }
    cout<<"DONE "<<tries<<" "<<ports<<" "<<passes<<" "<<nodes<<endl;
}

#endif
