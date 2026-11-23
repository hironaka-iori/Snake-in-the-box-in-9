#define DETOUR_LIBRARY
#include "free_outer_tips.cpp"
#include <map>
struct Site {int parent,at;string motif;};
int main(int argc,char** argv){
    if(argc!=5)return 2;
    ifstream in(argv[1]);int k=stoi(argv[2]),trials=stoi(argv[3]);mt19937 rng(stoul(argv[4]));
    vector<Path> donors;vector<Site> sites;unordered_map<string,vector<int>> classes;
    string word;
    while(in>>word){
        for(char& c:word)c='A'+c-'0';
        for(int orient=0;orient<2;orient++){
            int id=donors.size();donors.push_back(vertices(word));assert(valid(donors.back()));
            for(int i=37;i+k+37<int(word.size());i++){
                string motif=word.substr(i,k);classes[canonical(motif)].push_back(sites.size());
                sites.push_back({id,i,motif});
            }
            reverse(word.begin(),word.end());
        }
    }
    vector<Node> trie(1);uint64_t attempted=0,compatible=0,connections=0,bridgeCount=0,capped=0;
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
        int lcut=a.at+int(rng()%(k+1))-int(rng()%15);
        int rcut=b.at+int(rng()%(k+1))+int(rng()%15);
        int ltrim=rng()%6,rtrim=rng()%6;
        if(lcut<=ltrim || rcut>=int(q.size())-1-rtrim)continue;
        attempted++;
        Path left(p.begin()+ltrim,p.begin()+lcut+1);reverse(left.begin(),left.end());
        for(int& v:left)v^=p[lcut];
        Solver s(trie,left,192);int pin=b.at,delta=p[a.at]^p[lcut];
        auto trans=[&](int v){int out=delta;for(int mask=v^q[pin];mask;mask&=mask-1)out^=bits[countr_zero(unsigned(mask))];return out;};
        int first=trans(q[rcut]);if(first==0 || s.leftWithoutTip[first])continue;
        s.right.push_back(first);
        bool clash=false;
        for(int j=rcut+1;j<int(q.size())-rtrim;j++){
            int v=trans(q[j]);if(s.halo[v]){clash=true;break;}s.right.push_back(v);
        }
        if(clash)continue;
        compatible++;bool hit=s.glue();connections+=s.connected;bridgeCount+=s.deep;capped+=s.limits;
        if(int(s.best.size())-1>best){
            assert(valid(s.best));best=s.best.size()-1;cout<<"BEST "<<best;
            for(int v:s.best)cout<<" "<<v;cout<<endl;
        }
        if(hit || trial+1==trials){if(hit)break;}
        if(compatible%100000==0)cout<<"AT "<<trial<<" "<<compatible<<" "<<connections<<" "<<best<<endl;
    }
    cout<<"DONE "<<trials<<" "<<attempted<<" "<<compatible<<" "<<connections<<" "<<bridgeCount<<" "<<capped<<" "<<best<<endl;
}
