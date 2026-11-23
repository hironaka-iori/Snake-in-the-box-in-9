#include <fstream>
// Search paths contained in two placed Q8 snakes in the two layers of Q9.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <string>
#include <vector>
using namespace std;
using Path=vector<int>;
using Mask=array<uint64_t,4>;
bool valid(const Path& p,int dimension){
    for(int i=0;i<int(p.size());i++){
        if(p[i]<0||p[i]>=(1<<dimension))return false;
        for(int j=0;j<i;j++){
            int d=popcount(unsigned(p[i]^p[j]));
            if(!d||((d==1)!=(i==j+1)))return false;
        }
    }
    return true;
}
string word(const Path& p,bool reverse){
    int names[8];fill_n(names,8,-1);int count=0;string s;
    for(int k=1;k<int(p.size());k++){
        int i=reverse?int(p.size())-k:k;
        int d=countr_zero(unsigned(p[i]^p[i-1]));
        if(names[d]<0)names[d]=count++;
        s+=char('0'+names[d]);
    }
    return s;
}
struct Refill{
    array<bool,512> used{};Path vertices;
    int goal;unsigned long long nodes=0;
    Path refill_external(int left,int extra){
        if(extra==0)return visit(left);
        nodes++;
        int star=-1,high=2,excess=0;
        array<int,9> arms{};
        for(int v:vertices)if(used[v]){
            array<int,9> local{};int count=0;
            for(int d=0;d<9;d++)if(used[v^(1<<d)])local[count++]=v^(1<<d);
            if(count>2)excess++;
            if(count>high){star=v;high=count;arms=local;}
        }
        if(star>=0){
            if(excess>(high+1)*left || left==0)return {};
            used[star]=false;auto path=refill_external(left-1,extra);used[star]=true;
            if(!path.empty())return path;
            // Keeping the center forces all but at most two of its neighbors out.
            if(high-2>left)return {};
            for(int i=0;i<high;i++)for(int j=i+1;j<high;j++){
                for(int k=0;k<high;k++)if(k!=i&&k!=j)used[arms[k]]=false;
                path=refill_external(left-high+2,extra);
                for(int k=0;k<high;k++)if(k!=i&&k!=j)used[arms[k]]=true;
                if(!path.empty())return path;
            }
            return {};
        }
        array<bool,512> seen{},in_host{};
        array<int,512> contacts{};
        vector<int> sizes;
        for(int v:vertices)in_host[v]=true;
        for(int v:vertices)if(used[v]&&!seen[v]){
            Path comp{v};seen[v]=true;
            for(size_t i=0;i<comp.size();i++)for(int d=0;d<9;d++){
                int x=comp[i]^(1<<d);
                if(!in_host[x])contacts[x]++;
                if(used[x]&&!seen[x]){comp.push_back(x);seen[x]=true;}
            }
            sizes.push_back(comp.size());
        }
        sort(sizes.begin(),sizes.end(),greater<int>());
        if(!sizes.empty() && sizes[0]>=goal+1){
            auto path=visit(0);if(!path.empty())return path;
        }
        int capacity=extra;
        for(int i=0;i<int(sizes.size())&&i<=extra;i++)capacity+=sizes[i];
        if(capacity<goal+1)return {};
        for(int v=0;v<512;v++)if(contacts[v] && contacts[v]<=left+2){
            vertices.push_back(v);used[v]=true;
            auto path=refill_external(left,extra-1);
            used[v]=false;vertices.pop_back();
            if(!path.empty())return path;
        }
        return {};
    }
    Path one_extra(int left){
        // Resolve any degree-three vertex of the original host before choosing
        // the external vertex: adding a vertex cannot remove an existing chord.
        int star=-1,excess=0;
        array<int,3> neighbors{};
        for(int v:vertices)if(used[v]){
            array<int,3> local{};int dcount=0;
            for(int d=0;d<9;d++)if(used[v^(1<<d)]){
                if(dcount>=3)abort();local[dcount++]=v^(1<<d);
            }
            if(dcount==3){excess++;star=v;neighbors=local;}
        }
        nodes++;
        if(excess>4*left)return {};
        if(star>=0){
            for(int x:{star,neighbors[0],neighbors[1],neighbors[2]}){
                used[x]=false;auto p=one_extra(left-1);used[x]=true;if(!p.empty())return p;
            }
            return {};
        }
        array<bool,512> seen{};int longest=0,second=0;
        for(int v:vertices)if(used[v]&&!seen[v]){
            Path c{v};seen[v]=true;
            for(size_t i=0;i<c.size();i++)for(int d=0;d<9;d++){
                int z=c[i]^(1<<d);
                if(used[z]&&!seen[z]){c.push_back(z);seen[z]=true;}
            }
            int size=int(c.size());
            if(size>longest){second=longest;longest=size;}else second=max(second,size);
        }
        if(longest+second+1<goal+1)return {};
        array<bool,512> near{},host{};
        for(int u:vertices)host[u]=true;
        for(int u:vertices)if(used[u])for(int d=0;d<9;d++)near[u^(1<<d)]=true;
        for(int z=0;z<512;z++)if(near[z]&&!host[z]){
            vertices.push_back(z);used[z]=true;auto p=visit(left);
            used[z]=false;vertices.pop_back();if(!p.empty())return p;
        }
        return {};
    }
    Path visit(int left){
        nodes++;
        for(int v:vertices)if(used[v]){
            Path adj;
            for(int d=0;d<9;d++)if(used[v^(1<<d)])adj.push_back(v^(1<<d));
            if(adj.size()<=2)continue;
            if(left==0)return {};
            adj.push_back(v);
            for(int u:adj){used[u]=false;Path q=visit(left-1);used[u]=true;if(!q.empty())return q;}
            return {};
        }
        array<bool,512> seen{};
        for(int base:vertices)if(used[base]&&!seen[base]){
            Path comp{base},ends;seen[base]=true;
            for(int h=0;h<int(comp.size());h++){
                int v=comp[h],deg=0;
                for(int d=0;d<9;d++){
                    int u=v^(1<<d);
                    if(used[u]){deg++;if(!seen[u]){comp.push_back(u);seen[u]=true;}}
                }
                if(deg<=1)ends.push_back(v);
            }
            if(int(comp.size())-int(ends.empty())<goal+1)continue;
            int start=ends.empty()?base:ends[0],last=-1;
            Path out{start};
            while(int(out.size())<goal+1){
                int next=-1;
                for(int d=0;d<9;d++){int u=out.back()^(1<<d);if(used[u]&&u!=last){next=u;break;}}
                if(next<0)abort();last=out.back();out.push_back(next);
            }
            if(!valid(out,9))abort();return out;
        }
        return {};
    }
};
#ifndef Q8_HOST_LIBRARY
int main(int argc,char**argv){
    if(argc==2 && (string(argv[1])=="--fixed"||string(argv[1])=="--fixed-extra"||string(argv[1])=="--fixed-two"||string(argv[1])=="--fixed-three"||string(argv[1])=="--fixed-four")){
        int extra=string(argv[1])=="--fixed-four"?4:string(argv[1])=="--fixed-three"?3:string(argv[1])=="--fixed-two"?2:int(string(argv[1])=="--fixed-extra");
        int target,na,nb;
        while(cin>>target>>na>>nb){
            if(target<1||na<1||nb<1||na>256||nb>256)return 2;
            Path a(na),b(nb);
            for(int& v:a)if(!(cin>>v))return 2;
            for(int& v:b)if(!(cin>>v))return 2;
            if(!valid(a,8)||!valid(b,8))return 3;
            Refill r;r.goal=target;r.vertices=a;
            for(int v:b)r.vertices.push_back(v+256);
            for(int v:r.vertices)r.used[v]=true;
            Path w;
            if(na+nb+extra>=target+1)w=r.refill_external(na+nb+extra-target-1,extra);
            cout<<(w.empty()?"NO":"FOUND");for(int v:w)cout<<" "<<v;cout<<endl;
        }
        return 0;
    }
    int extra=argc==5 && string(argv[4])=="--extra-four"?4:argc==5 && string(argv[4])=="--extra-three"?3:argc==5 && string(argv[4])=="--extra-two"?2:int(argc==5 && string(argv[4])=="--extra-one");
    if(argc!=4&&!extra)return 2;
    int goal=stoi(argv[1]),minlen=stoi(argv[2]),maxPairs=stoi(argv[3]);
    vector<Path> bank;set<string> keys;string line;
    while(cin>>line){if(int(line.size())<minlen)continue;Path p{0};
        for(char c:line){if(c<'0'||c>'7')return 3;p.push_back(p.back()^(1<<(c-'0')));}
        if(!valid(p,8))return 4;
        if(int(p.size())>=goal+1){
            cout<<"FOUND 0 0";for(int k=0;k<=goal;k++)cout<<" "<<p[k];cout<<endl;return 0;
        }
        string key=min(word(p,false),word(p,true));
        if(keys.insert(key).second)bank.push_back(p);
    }
    stable_sort(bank.begin(),bank.end(),[](auto&a,auto&b){return a.size()>b.size();});
    set<string> freshKeys;
    const char* freshFile=getenv("Q8_NEW_SHAPES_FILE");
    if(freshFile){
        ifstream in(freshFile);if(!in)return 6;
        string seq;while(in>>seq){Path p{0};for(char c:seq){if(c<'0'||c>'7')return 6;p.push_back(p.back()^(1<<(c-'0')));}
            if(!valid(p,8))return 6;freshKeys.insert(min(word(p,false),word(p,true)));}
    }
    vector<bool> fresh;
    for(const auto& p:bank)fresh.push_back(freshKeys.contains(min(word(p,false),word(p,true))));
    unsigned long long pairs=0,placements=0,filtered=0,nodes=0;
    for(int a=0;a<int(bank.size());a++){
        const auto& p=bank[a];
        if(2*p.size()+extra<goal+1)break;
        array<Mask,256> lower{};
        for(int t=0;t<256;t++)for(int v:p){int x=v^t;lower[t][x>>6]|=1ull<<(x&63);}
        for(int b=a;b<int(bank.size());b++){
            const auto& q=bank[b];
            int k=int(p.size()+q.size())+int(extra)-goal-1;
            if(k<0)break;
            if(freshFile&&!fresh[a]&&!fresh[b])continue;
            if(maxPairs&&pairs>=maxPairs)goto done;
            pairs++;
            array<int,8> perm{0,1,2,3,4,5,6,7};
            do{
                // Evaluate only path vertices, via the permuted transition sequence.
                Mask image{};Path mapped{0};image[0]=1;
                for(int j=1;j<int(q.size());j++){
                    int x=mapped.back()^(1<<perm[countr_zero(unsigned(q[j]^q[j-1]))]);
                    mapped.push_back(x);image[x>>6]|=1ull<<(x&63);
                }
                placements+=256;
                for(int t=0;t<256;t++){
                    int overlap=0;
                    for(int j=0;j<4;j++)overlap+=popcount(lower[t][j]&image[j]);
                    if((!extra&&!overlap)||overlap>2*k+1)continue;
                    filtered++;
                    Refill r;r.goal=goal;r.vertices=p;
                    for(int v:mapped)r.vertices.push_back(256+(v^t));
                    for(int v:r.vertices)r.used[v]=true;
                    Path result;
                    if(!extra)result=r.visit(k);
                    else if(extra==1)result=r.one_extra(k);
                    else result=r.refill_external(k,extra);
                    nodes+=r.nodes;
                    if(!result.empty()){
                        cout<<"FOUND "<<a<<" "<<b;for(int v:result)cout<<" "<<v;cout<<endl;return 0;
                    }
                }
            }while(next_permutation(perm.begin(),perm.end()));
        }
    }
    done:cout<<"NO_JOIN bank "<<bank.size()<<" pairs "<<pairs<<" placements "<<placements
        <<" eligible "<<filtered<<" deletion_nodes "<<nodes<<endl;
}

#endif
