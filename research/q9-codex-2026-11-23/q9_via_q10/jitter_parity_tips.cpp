#define DETOUR_LIBRARY
#include "free_outer_tips.cpp"
#include <map>
#include "parity_bridge.inc"
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
    if(argc!=5)return 2;
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
    vector<Node> trie(1);uint64_t attempted=0,compatible=0,connections=0,bridgeCount=0,capped=0;
    int best=0;
    for(int trial=0;trial<trials;trial++){
        const auto& a=sites[rng()%sites.size()];auto& bucket=classes[canonical(a.motif)];
        const auto& b=sites[bucket[rng()%bucket.size()]];
        if(a.parent/2==b.parent/2)continue;
        int offset=a.at-b.at; if(offset<0 || offset>48)continue;
        array<int,9> bits{};int used=0;
        for(int i=0;i<k;i++){int bit=1<<(a.motif[i]-'A');bits[b.motif[i]-'A']=bit;used|=bit;}
        vector<int> remaining;for(int z=1;z<512;z*=2)if(!(z&used))remaining.push_back(z);
        shuffle(remaining.begin(),remaining.end(),rng);for(int& bit:bits)if(!bit){bit=remaining.back();remaining.pop_back();}
        if(rng()%3==0){int i=rng()%9,j=rng()%9;swap(bits[i],bits[j]);}
        const auto& p=donors[a.parent];const auto& q=donors[b.parent];
        int lcut=a.at+int(rng()%(k+1))-int(rng()%16);
        int rcut=b.at+(lcut-a.at)+2*(1+int(rng()%4));
        int ltrim=int(rng()%4)*2+(lcut&1);
        int rtrim=int(rng()%4)*2+((int(q.size())-1-rcut)&1);
        attempted++;FlexBridge s;
        for(int j=ltrim;j<=lcut;j+=2)s.left.push_back(p[j]);
        for(int j=rcut;j<int(q.size())-rtrim;j+=2){
            int v=p[a.at];for(int mask=q[j]^q[b.at];mask;mask&=mask-1)v^=bits[countr_zero(unsigned(mask))];
            s.right.push_back(v);
        }
        if(!s.init())continue;
        compatible++;bool hit=s.join(1+int(rng()%7));
        capped+=s.visits>=s.limit;connections+=!s.best.empty();
        if(int(s.best.size())-1>best){best=s.best.size()-1;cout<<"BEST "<<best;
            for(int v:s.best)cout<<" "<<v;cout<<endl;}
        if(hit)break;
        if(compatible%100000==0)cout<<"AT "<<trial<<" "<<compatible<<" "<<connections<<" "<<best<<endl;
    }
    cout<<"DONE "<<trials<<" "<<attempted<<" "<<compatible<<" "<<connections<<" "<<bridgeCount<<" "<<capped<<" "<<best<<endl;
}
