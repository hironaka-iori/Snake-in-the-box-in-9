#define main unused_hinge_main
#include "hinge.cpp"
#undef main
#include <map>
#include <bitset>
struct Motif{int row,pos;};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    ifstream mothers(argv[1]),seeds(argv[2]);int k=stoi(argv[3]);vector<string> words;vector<Path> ps;
    unordered_map<string,vector<Motif>> index;string w;
    auto abc=[](string s){for(char& c:s)c='A'+c-'0';return s;};
    while(mothers>>w){w=abc(w);for(int o=0;o<2;o++){int id=words.size();words.push_back(w);ps.push_back(vertices(w));assert(valid(ps.back()));for(int j=0;j+k<=int(w.size());j++)index[canonical(w.substr(j,k))].push_back({id,j});reverse(w.begin(),w.end());}}
    int row=0;
    while(seeds>>w){
        w=abc(w);Path p=vertices(w);bitset<512> own;for(int v:p)own.set(v);int defects=0;
        for(int i=0;i<int(p.size());i++)for(int j=i+2;j<int(p.size());j++)defects+=popcount(unsigned(p[i]^p[j]))==1;
        if(w.size()!=192 || defects!=2)continue;
        cout<<"SEED "<<row;for(int x:p)cout<<" "<<x;cout<<endl;
        set<array<int,10>> transforms; // Per orientation, avoid recomputing a transform seen at another motif.
        vector<set<array<int,10>>> done(words.size());map<Path,int> donors;
        for(int pos=0;pos+k<=int(w.size());pos+=3){
            auto found=index.find(canonical(w.substr(pos,k)));if(found==index.end())continue;
            for(auto m:found->second){
                array<int,10> image{};int occupied=0;
                for(int i=0;i<k;i++){int b=1<<(w[pos+i]-'A');image[words[m.row][m.pos+i]-'A']=b;occupied|=b;}
                vector<int> free,axes;for(int d=0;d<9;d++){if(!image[d])axes.push_back(d);if(!(occupied&(1<<d)))free.push_back(1<<d);}
                int attempts=0;do{
                    for(int j=0;j<int(axes.size());j++)image[axes[j]]=free[j];
                    int shift=p[pos];for(int mask=ps[m.row][m.pos];mask;mask&=mask-1)shift^=image[countr_zero(unsigned(mask))];
                    image[9]=shift;if(!done[m.row].insert(image).second)continue;
                    int u=shift,count=own[u];Path d{u};
                    for(char c:words[m.row]){u^=image[c-'A'];d.push_back(u);count+=own[u];}
                    if(count>=135){sort(d.begin(),d.end());donors.try_emplace(d,count);}
                }while(++attempts<24 && next_permutation(free.begin(),free.end()));
            }
        }
        vector<pair<int,Path>> ordered;for(auto& [p,score]:donors)ordered.emplace_back(score,p);sort(ordered.rbegin(),ordered.rend());
        for(int i=0;i<min<int>(400,ordered.size());i++){cout<<"DONOR "<<row<<" "<<ordered[i].first;for(int x:ordered[i].second)cout<<" "<<x;cout<<'\n';}
        row++;
    }
}
