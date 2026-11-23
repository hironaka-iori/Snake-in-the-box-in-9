#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
using P=vector<int>;
using Support=bitset<256>;
static bool valid(const P& p){
    for(int j=0;j<int(p.size());++j)for(int i=0;i<j;++i){
        int d=popcount(unsigned(p[i]^p[j]));
        if(d==0 || ((d==1)!=(j==i+1)))return false;
    }
    return true;
}
struct Repair{
    P record; unsigned ties=0; bool capture=false;
    P p,first,last,group,shade;
    array<array<int,4>,3> delta{};
    vector<array<int,3>> index;
    Support fixed;int best=1000000,limit,nodes=0;bool cut=false;
    mt19937& rng;
    Repair(const string& w,const array<int,9>& order,int cap,mt19937& r):limit(cap),rng(r){
        array<int,9> cls{};array<int,3> current{};
        for(int g=0;g<3;g++){
            int a=1<<order[3*g],b=1<<order[3*g+1],c=1<<order[3*g+2];
            delta[g]={0,a^b,a^c,b^c};
            for(int k=0;k<3;k++)cls[order[3*g+k]]=g;
            current[g]=g;first.push_back(0);group.push_back(g);shade.push_back(0);
        }
        index.push_back(current);p.push_back(0);
        for(int i=0;i<int(w.size());i++){
            int d=w[i]-'0',g=cls[d];current[g]=group.size();
            first.push_back(i+1);group.push_back(g);shade.push_back(0);index.push_back(current);
            p.push_back(p.back()^(1<<d));
        }
        last=first;
        for(int i=0;i<int(p.size());i++)for(int k:index[i])last[k]=i;
        assert(first.size()<=fixed.size());
    }
    void toggle(int v,int by){for(int i=first[v];i<=last[v];++i)p[i]^=delta[group[v]][by];shade[v]^=by;}
    vector<pair<int,int>> errors()const{
        array<int,512> head;head.fill(-1);array<int,256> prev;
        vector<pair<int,int>> out;
        for(int j=0;j<int(p.size());j++){
            int v=p[j];
            for(int i=head[v];i>=0;i=prev[i])out.emplace_back(i,j);
            for(int b=1;b<512;b*=2)for(int i=head[v^b];i>=0;i=prev[i])if(i+1!=j)out.emplace_back(i,j);
            if(j && p[j]!=p[j-1] && !has_single_bit(unsigned(p[j]^p[j-1])))out.emplace_back(j-1,j);
            prev[j]=head[v];head[v]=j;
        }
        return out;
    }
    bool run(int left){
        if(++nodes>limit){cut=true;return false;}
        auto bad=errors();if(capture && int(bad.size())<=best){if(int(bad.size())<best)ties=0;if(rng()%++ties==0)record=p;}best=min(best,int(bad.size()));
        if(bad.empty()){assert(valid(p));return true;}
        if(!left)return false;
        vector<Support> sets;array<int,256> freq{}; P pivot;
        for(auto [i,j]:bad){
            Support s;P ids;
            for(int g=0;g<3;g++)if(index[i][g]!=index[j][g])for(int k:{index[i][g],index[j][g]})if(!fixed[k]){
                s.set(k);ids.push_back(k);++freq[k];
            }
            if(ids.empty())return false;
            if(pivot.empty()||ids.size()<pivot.size())pivot=ids;
            sets.push_back(s);
        }
        stable_sort(sets.begin(),sets.end(),[](const Support& a,const Support& b){return a.count()<b.count();});
        Support used;int need=0;
        for(const auto& s:sets)if((used&s).none()){used|=s;if(++need>left)return false;}
        shuffle(pivot.begin(),pivot.end(),rng);
        stable_sort(pivot.begin(),pivot.end(),[&](int a,int b){return freq[a]>freq[b];});
        for(int k:pivot){
            fixed.set(k);array<pair<int,int>,3> choices;
            for(int d=1;d<=3;d++){toggle(k,d);choices[d-1]={errors().size(),d};toggle(k,d);}
            sort(choices.begin(),choices.end());
            for(auto [cost,d]:choices){
                toggle(k,d);if(run(left-1))return true;toggle(k,d);
                if(cut)break;
            }
            if(cut)break;
        }
        for(int k:pivot)fixed.reset(k);
        return false;
    }
};
#ifndef GROUP_WALK_LIBRARY
int main(int argc,char**argv){
    if(argc!=7)return 2;string mode=argv[1];int target=stoi(argv[2]),edit=stoi(argv[3]),cap=stoi(argv[4]),jobs=stoi(argv[5]);
    mt19937 rng(stoul(argv[6]));vector<string> words;string w;while(cin>>w)words.push_back(w);
    array<int,9> order;iota(order.begin(),order.end(),0);
    for(int z=0;z<jobs;z++){
        int row=rng()%words.size();string start=words[row],s=start;shuffle(order.begin(),order.end(),rng);
        if(mode=="control"){s.resize(target);}
        else{
            if(rng()%2)reverse(s.begin(),s.end());
            while(int(s.size())<target){
                vector<pair<int,string>> options;set<string> unique;
                for(int k=0;k<70;k++){
                    string t=s;t.insert(rng()%(t.size()+1),1,char('0'+rng()%9));
                    if(unique.insert(t).second){Repair x(t,order,0,rng);options.emplace_back(x.errors().size(),t);}
                }
                sort(options.begin(),options.end());s=options[rng()%min(size_t(6),options.size())].second;
            }
        }
        Repair h(s,order,cap,rng);
        if(mode=="control"){set<int> mut;while(int(mut.size())<edit)mut.insert(rng()%h.first.size());for(int k:mut)h.toggle(k,1+rng()%3);}
        int initial=h.errors().size();bool answer=h.run(edit);
        cout<<z<<" "<<row<<" "<<target<<" "<<initial<<" "<<h.best<<" "<<h.nodes<<" "<<(answer?"FOUND":h.cut?"LIMIT":"EXHAUSTED")<<" ";
        for(int d:order)cout<<d;cout<<" "<<s;
        if(answer)for(int x:h.p)cout<<" "<<x;
        cout<<endl;if(answer&&mode!="control")return 0;
    }
}

#endif
