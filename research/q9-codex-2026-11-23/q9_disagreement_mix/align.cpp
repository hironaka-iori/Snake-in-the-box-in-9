// Select three overlap bands independently for each cross-bank pair.
#define main placed_mixing_entry
#include "search.cpp"
#undef main
#include <random>
#include <unordered_map>
struct Window{int start,delta;};
struct Parent{
    string word;
    Path p;
    array<bool,512> inside{};
    unordered_map<string,vector<Window>> spans;
    vector<string> forward;
    explicit Parent(string w):word(w),p{0}{
        for(char d:w)p.push_back(p.back()^(1<<(d-'0')));
        for(int v:p)inside[v]=true;
        for(int k=0;k+10<=int(w.size());++k){
            string t=w.substr(k,10);forward.push_back(normalized(t));spans[normalized(t)].push_back({k,1});
            reverse(t.begin(),t.end());spans[normalized(t)].push_back({k+10,-1});
        }
    }
};
vector<Parent> readBank(const char* name){
    ifstream in(name);vector<Parent> v;string s;while(in>>s)v.emplace_back(s);
    if(v.empty())throw runtime_error("empty bank");return v;
}
int main(int argc,char**argv){
    if(argc!=6&&argc!=7)return 2;
    auto A=readBank(argv[1]),B=readBank(argv[2]);int from=stoi(argv[3]),to=min(stoi(argv[4]),int(A.size()));
    set<string> saved;
    for(int i=from;i<to;++i){
        auto& a=A[i];int poses=0,limited=0,best=0;long long leaves=0,legal=0;
        for(int j=0;j<int(B.size());++j){
            if(argc==7 && j!=(17*i+5)%int(B.size()) && j!=(23*i+31)%int(B.size()))continue;
            auto& b=B[j];mt19937 gen(1261+i*int(B.size())+j);
            vector<int> starts;
            for(int k=0;k<int(a.forward.size());++k)if(b.spans.count(a.forward[k]))starts.push_back(k);
            if(starts.empty())continue;
            array<Path,3> top;array<int,3> overlap{-1,-1,-1};
            for(int t=0;t<56;++t){
                int k=starts[gen()%starts.size()];auto& group=b.spans.at(a.forward[k]);auto anchor=group[gen()%group.size()];
                array<int,9> perm;perm.fill(-1);array<bool,9> used{};
                for(int s=0;s<10;++s){
                    int dst=a.word[k+s]-'0',src=b.word[anchor.start+(anchor.delta>0?s:-1-s)]-'0';
                    perm[src]=dst;used[dst]=true;
                }
                vector<int> spare;for(int d=0;d<9;++d)if(!used[d])spare.push_back(d);
                shuffle(spare.begin(),spare.end(),gen);
                for(int& v:perm)if(v<0){v=spare.back();spare.pop_back();}
                int anchorValue=0;
                for(int d=0;d<9;++d)if(b.p[anchor.start]&(1<<d))anchorValue^=1<<perm[d];
                int v=a.p[k]^anchorValue,count=a.inside[v];Path q{v};
                for(char c:b.word){v^=1<<perm[c-'0'];q.push_back(v);count+=a.inside[v];}
                int bin=count<106?0:count<151?1:2;
                if(count>=60&&count>overlap[bin]){top[bin]=move(q);overlap[bin]=count;}
            }
            for(int band=0;band<3;++band)if(overlap[band]>=0){
                if(argc==7){
                    if(band==0)continue;
                    if(a.p.size()+2!=top[band].size())throw runtime_error("unequal input");
                    for(int v:a.p)cout<<v<<" ";
                    for(int t=1;t+1<int(top[band].size());++t)cout<<top[band][t]<<" ";
                    cout<<"\n";
                    continue;
                }
                ++poses;Mixer m(saved,stoi(argv[5]),188);m.setup(a.p,top[band]);
                bool hit=m.dfs(0,m.common.size(),0);leaves+=m.leaves;legal+=m.legal;
                limited+=m.expanded>=m.budget;best=max(best,m.best);
                if(hit){cout<<"HIT "<<i<<" "<<j<<" "<<band<<endl;return 0;}
            }
        }
        if(argc==7)continue;
        cout<<"B "<<i<<" "<<poses<<" "<<limited<<" "<<leaves<<" "<<legal<<" "<<best<<" "<<saved.size()<<endl;
    }
}
