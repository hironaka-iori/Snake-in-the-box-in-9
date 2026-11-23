// Allow one specified cube edge to be a chord, then rethread all vertices of the other color.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <set>
#include <sstream>
#include <fstream>
#include <cassert>
using Path=vector<int>;
string encode(const Path& p){
    string w;for(int i=1;i<p.size();i++)w+=char('0'+countr_zero(unsigned(p[i]^p[i-1])));
    auto norm=[](string a){array<int,9> labels;labels.fill(-1);int count=0;for(auto& c:a){int d=c-'0';if(labels[d]<0)labels[d]=count++;c='0'+labels[d];}return a;};
    auto f=norm(w);reverse(w.begin(),w.end());return min(f,norm(w));
}
struct Repair{
    int a,b,cap;set<string>& known;ostream& output;uint64_t tests=0,graphs=0,unknown=0,positive=0,fresh=0,lifts=0;
    bool run(Search& s){
        tests++;int n=s.fixed.size();int major=n==97;
        // Only the opposite-color endpoint sees a changed incidence mask.
        int fixedColor=popcount(unsigned(s.fixed[0]))%2;
        int x=(popcount(unsigned(a))%2==fixedColor)?a:b,y=x^a^b;
        if(s.slot[x]>=0)s.axes[y]^=x^y;
        bool hit=check(s,major);
        if(s.slot[x]>=0)s.axes[y]^=x^y;
        return hit;
    }
    bool check(Search& s,bool major){
        int n=s.fixed.size();array<int,512> degree{};int leaves=0,pairs=0;
        for(int v=0;v<512;v++){
            unsigned m=s.axes[v];int k=popcount(m);if(k==2)pairs++;else if(k==1){leaves++;if(major)continue;}else continue;
            while(m){degree[v^(1<<countr_zero(m))]++;m&=m-1;}
        }
        if(pairs<n-1||(!major&&leaves<2))return false;
        int low=0;for(int v:s.fixed){if(degree[v]<1)return false;low+=degree[v]==1;}
        if(low>(major?2:0))return false;
        Graph g(s.fixed,cap);graphs++;
        for(int v=0;v<512;v++){
            unsigned m=s.axes[v];int k=popcount(m);if(k!=2&&(major||k!=1))continue;
            int i=s.slot[v^(1<<countr_zero(m))];m&=m-1;
            int j=m?s.slot[v^(1<<countr_zero(m))]:g.dummy;g.add(i,j,v);
        }
        if(major)for(int i=0;i<n;i++)g.add(i,g.dummy,-1);
        int res=g.visit(vector<int8_t>(g.edges.size()));if(res<0)unknown++;if(res!=1)return false;
        positive++;
        auto p=g.witness;int parity=major?1:0;vector<int> sites;vector<Path> opts;
        for(int i=parity;i<p.size();i+=2){
            int v=i?p[i-1]:p[i+1];Path choices;
            for(int d=0;d<9;d++){
                int z=v^(1<<d);unsigned m=s.axes[z];if(!(m&(1<<d)))continue;
                if(i>0&&i+1<p.size()){
                    unsigned other=z^p[i+1];if(!has_single_bit(other)||popcount(m)!=2||!(m&other))continue;
                }else if(popcount(m)!=1)continue;
                choices.push_back(z);
            }
            if(choices.size()>1){sites.push_back(i);opts.push_back(choices);}
        }
        auto enumerate=[&](auto&& self,int pos)->bool{
            if(pos<sites.size()){for(int v:opts[pos]){p[sites[pos]]=v;if(self(self,pos+1))return true;}return false;}
            lifts++;assert(p.size()==193);int chords=0;
            for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){
                int d=popcount(unsigned(p[i]^p[j]));assert(d && (i!=j+1||d==1));
                if(i!=j+1 && d==1){assert((p[i]==a&&p[j]==b)||(p[i]==b&&p[j]==a));chords++;}
            }
            if(!chords){cout<<"FOUND";for(int v:p)cout<<" "<<v;cout<<endl;return true;}
            assert(chords==1);auto w=encode(p);if(known.insert(w).second){fresh++;output<<w<<endl;}return false;
        };
        return enumerate(enumerate,0);
    }
};
int main(int argc,char**argv){
    if(argc!=5)return 2;int maxChord=stoi(argv[1]),moves=stoi(argv[2]);if(moves>1)return 2;
    set<string> known;string line;ifstream old(argv[3]);if(!old)return 2;
    while(getline(old,line)){istringstream in(line);Path p;int x;while(in>>x)p.push_back(x);if(p.size()!=193)return 3;known.insert(encode(p));}
    ofstream out(argv[4]);if(!out)return 3;int lost;string w;int row=0;
    while(cin>>lost>>w){
        if(lost>maxChord)continue;Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
        vector<pair<int,int>> bad;for(int j=0;j<p.size();j++)for(int i=0;i+1<j;i++)if(popcount(unsigned(p[i]^p[j]))==1)bad.push_back({p[i],p[j]});
        assert(bad.size()==lost&&p.size()==193);
        uint64_t tests=0,graphs=0,unknown=0,positive=0,lifts=0,fresh=0;
        for(auto [a,b]:bad)for(int side=0;side<2;side++){
            Path s;for(int i=side;i<p.size();i+=2)s.push_back(p[i]);Search state(s,100000);Repair r{a,b,100000,known,out};
            if(r.run(state))return 0;
            if(moves){Path pool;for(int v=0;v<512;v++)if(state.slot[v]<0&&popcount(unsigned(v^s[0]))%2==0)pool.push_back(v);
                for(int j=0;j<s.size();j++){
                    int prev=s[j];state.toggle(prev,j,false);
                    for(int v:pool){
                        state.fixed[j]=v;state.toggle(v,j,true);
                        if(r.run(state))return 0;state.toggle(v,j,false);
                    }
                    state.fixed[j]=prev;state.toggle(prev,j,true);
                }
            }
            tests+=r.tests;graphs+=r.graphs;unknown+=r.unknown;positive+=r.positive;lifts+=r.lifts;fresh+=r.fresh;
        }
        cout<<"ROW "<<row++<<" "<<tests<<" "<<graphs<<" "<<unknown<<" "<<positive<<" "<<lifts<<" "<<fresh<<endl;
    }
}
