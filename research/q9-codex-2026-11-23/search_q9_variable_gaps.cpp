// Select all bridge lengths jointly so that the assembled induced path has the target length.
#define main short_route_cli
#include "search_q9_short_route_join.cpp"
#undef main
string canonicalWord(const Path& p){
    string w;for(int i=1;i<p.size();i++)w.push_back(char(48+countr_zero(unsigned(p[i]^p[i-1]))));
    auto normalize=[](string a){
        array<int,9> labels;labels.fill(-1);int next=0;
        for(char& c:a){int d=c-48;if(labels[d]<0)labels[d]=next++;c=char(48+labels[d]);}
        return a;
    };
    string f=normalize(w);reverse(w.begin(),w.end());return min(f,normalize(w));
}
struct VariableGaps{
    set<string>* exclude=nullptr;
    uint64_t seen_known=0;
    Join j;
    vector<Path> islands;vector<vector<Route>> opts;
    vector<int> chosen;
    Path witness;
    int budget,wanted,optionCap;
    uint64_t nodes=0;
    bool limited=false;
    bool assemble(vector<vector<int>>& domains,int need,int missing){
        if(++nodes>uint64_t(budget)){limited=true;return false;}
        if(!missing){
            if(need)return false;
            witness=opts.front()[chosen.front()].path;reverse(witness.begin(),witness.end());
            for(int i=0;i<islands.size();i++){
                witness.insert(witness.end(),islands[i].begin(),islands[i].end());
                auto& route=opts[i+1][chosen[i+1]].path;witness.insert(witness.end(),route.begin(),route.end());
            }
            assert(int(witness.size())==wanted && valid(witness));
            if(exclude && exclude->contains(canonicalWord(witness))){seen_known++;return false;}
            return true;
        }
        int next=-1,lo=0,hi=0;
        for(int i=0;i<domains.size();i++)if(chosen[i]<0){
            auto& d=domains[i];if(d.empty())return false;
            lo+=opts[i][d.back()].path.size();hi+=opts[i][d.front()].path.size();
            if(next<0||d.size()<domains[next].size())next=i;
        }
        if(need<lo||need>hi)return false;
        for(int idx:domains[next]){
            auto& r=opts[next][idx];int length=r.path.size();
            if(length>need)continue;
            if(need-length>hi-int(opts[next][domains[next].front()].path.size()))continue;
            if(need-length<lo-int(opts[next][domains[next].back()].path.size()))continue;
            auto child=domains;chosen[next]=idx;bool ok=true;
            for(int i=0;i<domains.size()&&ok;i++)if(chosen[i]<0){
                auto& d=child[i];d.erase(remove_if(d.begin(),d.end(),[&](int k){return contact(r.boundary,opts[i][k].set);}),d.end());ok=!d.empty();
            }
            if(ok&&assemble(child,need-length,missing-1))return true;
            chosen[next]=-1;if(limited)return false;
        }return false;
    }
    bool search(const Path&p,vector<pair<int,int>> pieces,int target,int extra,int cap,int maxOptions){
        budget=cap;optionCap=maxOptions;wanted=target+1;j.perPool=maxOptions;
        int kept=0;
        for(auto [a,b]:pieces){
            Path island(p.begin()+a,p.begin()+b+1);
            if(!valid(island))return false;
            for(int v:island)if(j.used[v]||j.touch[v])return false;
            for(int v:island)j.mark(v,1);
            kept+=island.size();islands.push_back(move(island));
        }
        auto routes=[&](int from,int to,int maxlen){
            opts.emplace_back();auto& list=opts.back();Path inside;
            int low=to<0?0:distanceQ(from,to);
            for(int len=low;len<=maxlen;len+=(to<0?1:2)){
                j.fill(from,to,len,inside,list);if(j.limited){limited=true;return false;}
            }
            reverse(list.begin(),list.end());return !list.empty();
        };
        if(!routes(islands.front().front(),-1,pieces.front().first+extra))return false;
        for(int i=1;i<pieces.size();i++)
            if(!routes(islands[i-1].back(),islands[i].front(),pieces[i].first-pieces[i-1].second+extra))return false;
        if(!routes(islands.back().back(),-1,int(p.size())-1-pieces.back().second+extra))return false;
        vector<vector<int>> dom(opts.size());
        for(int i=0;i<dom.size();i++){dom[i].resize(opts[i].size());iota(dom[i].begin(),dom[i].end(),0);}
        chosen.assign(opts.size(),-1);return assemble(dom,wanted-kept,dom.size());
    }
};
int main(int argc,char**argv){
    if(argc==2 && string(argv[1])=="query"){
        string line;while(getline(cin,line)){
            istringstream in(line);int goal,extra,count,v,number,a,b;
            if(!(in>>goal>>extra>>count))return 2;
            Path p;for(int i=0;i<count;i++){if(!(in>>v))return 2;p.push_back(v);}
            in>>number;vector<pair<int,int>> pieces;
            for(int i=0;i<number;i++){if(!(in>>a>>b)||a<0||b<a||b>=count)return 2;pieces.push_back({a,b});}
            if(!valid(p)||pieces.empty())return 2;
            VariableGaps g;if(g.search(p,pieces,goal,extra,1000000,200000)){
                cout<<"YES";for(int x:g.witness)cout<<" "<<x;cout<<endl;
            }else cout<<(g.limited?"UNKNOWN":"NO")<<endl;
        }return 0;
    }
    if(argc!=8 && argc!=10)return 2;
    set<string> exclude;bool harvest=argc==10;ofstream output;
    if(harvest){ifstream input(argv[8]);if(!input)return 2;string w;
        while(input>>w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-48)));exclude.insert(canonicalWord(p));}
        output.open(argv[9],ios::app);if(!output)return 2;
    }
    int trials=stoi(argv[1]),target=stoi(argv[2]),seed=stoi(argv[3]),extra=stoi(argv[4]),gap=stoi(argv[5]),cap=stoi(argv[6]),pool=stoi(argv[7]);
    vector<Path> bank;string l;while(getline(cin,l)){Path p{0};for(char c:l){if(c<'0'||c>'8')return 2;p.push_back(p.back()^(1<<(c-'0')));}if(!valid(p))return 3;bank.push_back(p);}
    mt19937 gen(seed);uint64_t cuts=0,nodes=0,hits=0,skipped=0;
    for(int t=0;t<trials;t++){
        auto id=gen()%bank.size();auto& p=bank[id];int start=gen()%4,end=int(p.size())-1-gen()%4;
        vector<pair<int,int>> pieces;
        while(start<=end){
            int last=min(end,start+1+int(gen()%6));pieces.push_back({start,last});
            start=last+2+gen()%gap;
        }
        VariableGaps g;if(harvest)g.exclude=&exclude;
        bool found=g.search(p,pieces,target,extra,cap,pool);cuts+=g.limited;nodes+=g.nodes;skipped+=g.seen_known;
        if(found&&harvest){
            auto key=canonicalWord(g.witness);assert(exclude.insert(key).second);hits++;output<<key<<endl;
            for(int side=0;side<2;side++){for(int d=0;d<9;d++){Path q=g.witness;q.push_back(q.back()^(1<<d));
                if(q.size()>=193 && valid(q)){cout<<"EXTENDED";for(int v:q)cout<<" "<<v;cout<<endl;return 0;}}
                reverse(g.witness.begin(),g.witness.end());}
        }
        if(found&&!harvest){cout<<"FOUND "<<id<<" "<<t;for(int v:g.witness)cout<<" "<<v;cout<<endl;return 0;}
        if((t+1)%10000==0||t+1==trials)cout<<"AT "<<t+1<<" "<<cuts<<" "<<nodes<<" "<<hits<<" "<<skipped<<endl;
    }
}
