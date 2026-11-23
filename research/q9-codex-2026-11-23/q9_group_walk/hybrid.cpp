#define GROUP_CROSS_LIBRARY
#include "cross.cpp"
struct Table{
    int t;array<int,512> price{};
    array<array<int,10>,10> costs{};
};
struct Search{
    const Pattern& pat;const Shape& src;const Table& h;int budget;
    array<int,512> mapped{};array<bool,512> atend{};
    Search(const Pattern& a,const Shape& b,const Table& c,int k):pat(a),src(b),h(c),budget(k){
        for(int j=b.p.size()-5;j<int(b.p.size());j++)atend[b.p[j]]=true;
    }
    bool walk(int lv,int left,int used,int cost){
        if(lv==9)return true;
        int bit=1<<pat.axes[lv];
        for(int bits=left;bits;bits&=bits-1){
            int dest=bits&-bits;
            for(int m=used;;m=(m-1)&used){mapped[m|bit]=mapped[m]|dest;if(!m)break;}
            int loss=cost;
            for(int v:pat.ready[lv]){
                int c=h.price[mapped[v]];
                if(c && atend[v]){loss=100;break;}
                loss+=c;if(loss>budget)break;
            }
            if(loss<=budget && walk(lv+1,left^dest,used|bit,loss))return true;
        }
        return false;
    }
};
vector<Table> tables(const Shape& a,int budget){
    array<int,512> occ{},deg{},early{};
    for(int j=0;j<int(a.p.size());j++){int v=a.p[j];occ[v]=1;
        for(int bit=1;bit<512;bit*=2){deg[v^bit]++;if(j<5)early[v^bit]=1;}}
    vector<Table> out;
    for(int bit=1;bit<512;bit*=2){
        int t=a.p.back()^bit;if(occ[t]||early[t]||deg[t]-1>budget)continue;Table h;h.t=t;
        for(int z=0;z<512;z++){int v=t^z;int cost=(occ[v]||early[v])?12:deg[v]-(z==0);
            h.price[z]=cost;if(cost<=9)h.costs[popcount(unsigned(z))][cost]++;}
        out.push_back(h);
    }return out;
}
int main(int argc,char**argv){
    if(argc!=6)return 2;
    int len=stoi(argv[1]),cap=stoi(argv[2]),budget=stoi(argv[3]);mt19937 rng(stoul(argv[4]));bool keepKnown=cap<0;cap=abs(cap);string line;
    unordered_set<string> baseline[2],raw[2];ifstream kfile(argv[5]);
    for(string w;kfile>>w;){Shape s=shape(w);windows(s.p,len,baseline[0]);windows(s.p,191-len,baseline[1]);}
    while(getline(cin,line)){istringstream in(line);Path p;for(int v;in>>v;)p.push_back(v);windows(p,len,raw[0]);windows(p,191-len,raw[1]);}
    vector<Shape> arms[2];vector<Pattern> pre;
    for(int i=0;i<2;i++){auto& s=raw[i];vector<string> words;
        for(const auto& w:s)if(keepKnown||!baseline[i].count(w))words.push_back(w);
        sort(words.begin(),words.end());shuffle(words.begin(),words.end(),rng);
        if(words.size()>cap)words.resize(cap);
        if(i){vector<string> more(baseline[i].begin(),baseline[i].end());sort(more.begin(),more.end());shuffle(more.begin(),more.end(),rng);
            words.insert(words.end(),more.begin(),more.begin()+min(more.size(),size_t(cap)));}
        for(auto& w:words)arms[i].push_back(shape(w));
    }
    for(auto& b:arms[1])pre.emplace_back(b);
    cout<<"BANK "<<arms[0].size()<<" "<<arms[1].size()<<endl;uint64_t checks=0,passes=0,hits=0;
    for(const auto& a:arms[0]){
        auto hs=tables(a,budget);
        for(int j=0;j<int(arms[1].size());j++){auto& b=arms[1][j];int best=budget+1;
            for(const auto& h:hs){checks++;int lb=0;
                for(int d=0;d<=9;d++){int n=b.demand[d];
                    for(int c=0;c<=budget&&n;c++){int x=min(n,h.costs[d][c]);lb+=c*x;n-=x;}
                    if(n||lb>=best){lb=99;break;}}
                if(lb>=best)continue;
                Search search(pre[j],b,h,best-1);passes++;
                if(search.walk(0,511,0,h.price[0])){
                    Path p=a.p;for(int v:b.p)p.push_back(h.t^search.mapped[v]);int defects=0;
                    for(int y=0;y<int(p.size());y++)for(int x=0;x<y;x++){
                        int d=popcount(unsigned(p[x]^p[y]));assert(d>0);
                        if(x+1==y)assert(d==1);else if(d==1){assert(x>=5&&y+5<int(p.size()));defects++;}
                    }
                    assert(defects<best);best=defects;hits++;
                    cout<<(best?"NEAR":"FOUND")<<" "<<best;for(int v:p)cout<<" "<<v;cout<<endl;
                    if(!best)return 0;
                    if(best==1)break;
                }
            }
        }
        if((&a-&arms[0][0])%20==0)cout<<"CHECK "<<checks<<" "<<passes<<" "<<hits<<endl;
    }cout<<"DONE "<<checks<<" "<<passes<<" "<<hits<<endl;
}
