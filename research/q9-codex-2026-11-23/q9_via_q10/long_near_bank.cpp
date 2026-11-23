#define DETOUR_LIBRARY
#include "free_outer_tips.cpp"
#include <map>
#include "parity_bridge.inc"
#include <map>
struct Site {int parent,at;string motif;};
int main(int argc,char** argv){
    if(argc==3 && string(argv[1])=="--plant"){
        ifstream input(argv[2]);string w;int n=0,good=0;
        while(input>>w){for(char& c:w)c='A'+c-'0';auto path=vertices(w);FlexBridge s;
            for(int i=0;i<=92;i+=2)s.left.push_back(path[i]);
            for(int i=96;i<=190;i+=2)s.right.push_back(path[i]);
            assert(s.init());s.join(1);good+=s.best.size()>=192 && valid(s.best);n++;
        }
        cout<<"CONTROL "<<good<<" "<<n<<endl;return good==n?0:1;
    }
    if(argc!=6)return 2;
    ifstream in(argv[1]);int k=stoi(argv[2]),trials=stoi(argv[3]);mt19937 rng(stoul(argv[4]));
    vector<Path> donors;vector<Site> sites;unordered_map<string,vector<int>> classes;
    string word;
    while(in>>word){
        for(char& c:word)c='A'+c-'0';
        for(int orient=0;orient<2;orient++){
            int id=donors.size();donors.push_back(vertices(word));/* Donors may have chords. Reconstructed candidates must pass valid(). */
            for(int i=37;i+k+37<int(word.size());i++){
                string motif=word.substr(i,k);classes[canonical(motif)].push_back(sites.size());
                sites.push_back({id,i,motif});
            }
            reverse(word.begin(),word.end());
        }
    }
    int target=stoi(argv[5]);set<string> seen;int counts[19]{}; vector<Node> trie(1);uint64_t attempted=0,compatible=0,connections=0,bridgeCount=0,capped=0;
    int best=0;
    for(int trial=0;trial<trials;trial++){
        const auto& a=sites[rng()%sites.size()];auto& bucket=classes[canonical(a.motif)];
        const auto& b=sites[bucket[rng()%bucket.size()]];
        if(a.parent/2==b.parent/2)continue;
        int offset=a.at-b.at; if(offset<0 || offset>32)continue;
        array<int,9> bits{};int used=0;
        for(int i=0;i<k;i++){int bit=1<<(a.motif[i]-'A');bits[b.motif[i]-'A']=bit;used|=bit;}
        vector<int> remaining;for(int z=1;z<512;z*=2)if(!(z&used))remaining.push_back(z);
        shuffle(remaining.begin(),remaining.end(),rng);for(int& bit:bits)if(!bit){bit=remaining.back();remaining.pop_back();}
        const auto& p=donors[a.parent];const auto& q=donors[b.parent];
        int cut=a.at+int(rng()%(k+1));Path path(p.begin(),p.begin()+cut+1);
        for(int j=b.at+cut-a.at+1;j<int(q.size());j++){
            int v=p[a.at];for(int mask=q[j]^q[b.at];mask;mask&=mask-1)v^=bits[countr_zero(unsigned(mask))];
            path.push_back(v);
        }
        if(int(path.size())<target+1)continue;
        int first=rng()%(path.size()-target);
        Path part(path.begin()+first,path.begin()+first+target+1);
        if(cut-first<20||cut-first>target-20)continue;
        array<int,512> load{},usedEven{};
        bool dup=false;for(int j=0;j<=target;j+=2){int v=part[j];if(usedEven[v]++){dup=true;break;}for(int z=1;z<512;z*=2)load[v^z]++;}
        if(dup)continue;
        int score=0;for(int j=0;j+2<=target;j+=2){
            int u=part[j],v=part[j+2],z=u^v,a=z&-z,b=z^a;if(!b){score=99;break;}
            score+=min(load[u^a],load[u^b])-2;if(score>18)break;
        }
        if(target%2){int v=part[target-1],low=20;for(int bit=1;bit<512;bit*=2)low=min(low,load[v^bit]);score+=low-1;}
        if(score>18)continue;
        string label;for(int j=1;j<=target;j++){unsigned mask=part[j]^part[j-1];assert(has_single_bit(mask));label.push_back('A'+countr_zero(mask));}
        string key=canonical(label);reverse(label.begin(),label.end());key=min(key,canonical(label));
        if(!seen.insert(key).second)continue;
        if(score==0){
            Path full{part[0]};for(int j=0;j+2<=target;j+=2){int u=part[j],v=part[j+2],z=u^v,a=z&-z,b=z^a;full.push_back(load[u^a]==2?u^a:u^b);full.push_back(v);}
            if(target%2){int tip=full.back();for(int bit=1;bit<512;bit*=2)if(load[tip^bit]==1){full.push_back(tip^bit);break;}}
            assert(int(full.size())==target+1&&valid(full));cout<<"FOUND "<<target;for(int v:full)cout<<" "<<v;cout<<endl;return 0;
        }
        if(counts[score]>=450)continue;
        counts[score]++;cout<<"SEED "<<score;for(int v:part)cout<<" "<<v;cout<<'\n';
    }
    cerr<<"SCORES";for(int n:counts)cerr<<" "<<n;cerr<<endl;

}
