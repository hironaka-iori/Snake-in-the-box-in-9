#define Q9_TIP_LIBRARY
#include "q9_catalogue_tip_core.cpp"
#include <unordered_set>

struct JoinSearch {
    Search extension;
    unordered_set<string> completed, fragmentPairs;
    uint64_t reused=0;
    vector<int> first,second,middle;
    array<bool,512> reachable{};
    uint64_t orientations=0,bridgeNodes=0,joins=0,distinctVisits=0;

    static bool adjacent(int x,int y){return popcount(unsigned(x^y))==1;}
    bool acceptBridge(){
        ++joins;
        vector<int>& path=extension.core;
        path=first;
        path.insert(path.end(),middle.begin(),middle.end());
        path.insert(path.end(),second.begin(),second.end());
        string word;
        for(size_t k=1;k<path.size();k++)word+=char('0'+countr_zero(unsigned(path[k]^path[k-1])));
        if(completed.size()>500000)completed.clear();
        if(!completed.insert(canonical(word)).second)return false;
        ++distinctVisits;
        return extension.dfs(path.front(),path.back(),true,int(path.size()));
    }
    bool bridge(int tip){
        ++bridgeNodes;
        for(int d=0;d<extension.dimensions;d++){
            int v=tip^(1<<d);
            if(extension.used[v])continue;
            bool last=adjacent(v,second.front());
            if(extension.near[v]!=(last?2:1))continue;
            if(!last&&!reachable[v])continue;
            extension.mark(v,1);middle.push_back(v);
            bool success=last?acceptBridge():bridge(v);
            middle.pop_back();extension.mark(v,-1);
            if(success)return true;
        }
        return false;
    }
    bool orient(){
        ++orientations;
        reachable.fill(false);
        vector<int> queue;
        for(int d=0;d<extension.dimensions;d++){
            int y=second.front()^(1<<d);
            if(extension.used[y])continue;
            if(extension.near[y]==1){queue.push_back(y);reachable[y]=true;}
        }
        for(size_t k=0;k<queue.size();k++)for(int d=0;d<extension.dimensions;d++){
            int y=queue[k]^(1<<d);
            if(reachable[y]||extension.used[y])continue;
            if(!extension.near[y]||(extension.near[y]==1&&adjacent(y,first.back()))){
                reachable[y]=true;
                if(!extension.near[y])queue.push_back(y);
            }
        }
        return bridge(first.back());
    }
    bool translate=false,swapAxes=false;
    uint64_t shifts=0, viable=0, linked=0;
    bool run(const vector<int>& v,int l,int r,int start,int gap){
        first.assign(v.begin()+l,v.begin()+start+1);
        second.assign(v.begin()+start+gap+1,v.end()-r);
        if(!translate)return placed(false);
        array<bool,512> taken{};
        array<int,512> contact{};
        for(int x:first){
            taken[x]=true;
            for(int d=0;d<extension.dimensions;d++)contact[x^(1<<d)]++;
        }
        const vector<int> original=second;
        vector<pair<int,int>> swaps{{0,0}};
        if(swapAxes)for(int a=0;a<extension.dimensions;a++)for(int b=a+1;b<extension.dimensions;b++)swaps.emplace_back(a,b);
        for(auto [a,b]:swaps){
        vector<int> base=original;
        if(a!=b)for(int& y:base)if(((y>>a)^(y>>b))&1)y^=(1<<a)|(1<<b);
        for(int t=0;t<(1<<extension.dimensions);t++){
            ++shifts;
            int edges=0;
            for(int x:base){
                int y=x^t;
                edges+=contact[y];
                if(taken[y]||edges>1){edges=2;break;}
            }
            if(edges>1)continue;
            if(edges==1){
                bool ends=false;
                for(int a:{first.front(),first.back()})for(int b:{base.front(),base.back()})
                    ends|=adjacent(a,b^t);
                if(!ends)continue;
                ++linked;
            }
            ++viable;
            for(size_t k=0;k<base.size();k++)second[k]=base[k]^t;
            if(placed(edges==1))return true;
        }
        }
        return false;
    }
    bool placed(bool direct){
        // Store both ordered transition words and the relative translation.
        // This removes only duplicates related by one simultaneous cube isometry.
        array<int,9> axis;
        axis.fill(-1);
        int next=0;
        string key;
        for(const auto* piece:{&first,&second}){
            for(size_t j=1;j<piece->size();j++){
                int d=countr_zero(unsigned((*piece)[j]^(*piece)[j-1]));
                if(axis[d]<0)axis[d]=next++;
                key+=char(48+axis[d]);
            }
            key+=char(47);
        }
        int offset=first.front()^second.front(), relative=0;
        for(int d=0;d<extension.dimensions;d++)if(offset&(1<<d)){
            if(axis[d]<0)axis[d]=next++;
            relative|=1<<axis[d];
        }
        key+=char(relative>>8);key+=char(relative&255);
        if(fragmentPairs.size()>=200000)fragmentPairs.clear();
        if(!fragmentPairs.insert(key).second){reused++;return false;}
        for(auto& p:{first,second})for(int x:p)extension.mark(x,1);
        for(int a=0;a<2;a++,reverse(first.begin(),first.end()))
            for(int b=0;b<2;b++,reverse(second.begin(),second.end()))
                if(direct?(adjacent(first.back(),second.front())&&acceptBridge()):orient())return true;
        for(auto& p:{first,second})for(int x:p)extension.mark(x,-1);
        return false;
    }
};
#ifndef Q9_FRAGMENT_LIBRARY
int main(int argc,char**argv){
    if(argc<7)return 2;
    int goal=stoi(argv[1]),trim=stoi(argv[2]),gap=stoi(argv[3]),stride=stoi(argv[4]),cutStep=stoi(argv[5]);
    if(gap<1||trim<0||stride<1||cutStep<1)return 2;
    set<string> parents;
    for(int i=6;i<argc;i++){ifstream f(argv[i]);if(!f)throw runtime_error("file");string w;while(f>>w)parents.insert(canonical(w));}
    JoinSearch s;s.extension.goal=goal;s.translate=std::getenv("Q9_TRANSLATE");s.swapAxes=std::getenv("Q9_AXIS_SWAP");int count=0;uint64_t tests=0;
    for(auto&w:parents){
        vector<int> v{0};for(char d:w)v.push_back(v.back()^(1<<(d-'0')));
        for(size_t j=0;j<v.size();j++)for(size_t i=0;i<j;i++)
            if(v[i]==v[j]||(s.adjacent(v[i],v[j])!=(i+1==j)))throw runtime_error("invalid parent");
        for(int l=0;l<=trim;l++)if(l%stride==0||l==trim){
            int r=trim-l;
            for(int i=l+1;i+gap+2<int(v.size())-r;i+=cutStep){
                ++tests;if(s.run(v,l,r,i,gap))return 0;
            }
        }
        if(++count%100==0)cout<<"AT "<<count<<" "<<tests<<" "<<s.bridgeNodes<<" "<<s.extension.nodes<<endl;
    }
    cout<<"DONE "<<goal<<" "<<trim<<" "<<gap<<" "<<stride<<" "<<cutStep<<" "<<count<<" "<<tests<<" "<<s.orientations<<" "<<s.bridgeNodes<<" "<<s.joins<<" "<<s.distinctVisits<<" "<<s.extension.nodes<<" "<<s.reused<<" "<<s.shifts<<" "<<s.viable<<" "<<s.linked<<endl;
}
#endif
