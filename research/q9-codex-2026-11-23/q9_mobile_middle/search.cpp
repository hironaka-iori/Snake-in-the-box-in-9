// Reposition a long middle interval, then reconstruct the far seam in the full Q9.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using namespace std;
using Path = vector<int>;
int distance9(int a,int b){return popcount(unsigned(a^b));}
bool snake(const Path& p){
    for(int i=0;i<int(p.size());++i)for(int j=0;j<i;++j)
        if(p[i]==p[j] || ((j==i-1)!=(distance9(p[i],p[j])==1)))return false;
    return true;
}
struct Search{
    int target, gap, stride, budget, lead;
    long long geometries=0, candidates=0, nodes=0, cutoffs=0;
    array<int,512> blocked{},occupied{};
    int used=0;bool cut=false;Path bridge,answer;
    void mark(int v,int delta){
        occupied[v]+=delta;
        for(int d=0;d<9;++d)blocked[v^(1<<d)]+=delta;
    }
    bool connect(int u,int v,int length){
        if(length==1)return distance9(u,v)==1;
        if(distance9(u,v)>length || ((distance9(u,v)^length)&1))return false;
        if(used>=budget){cut=true;return false;}
        ++used;++nodes;
        for(int d=0;d<9;++d){
            int x=u^(1<<d);
            if(occupied[x] || blocked[x]!=(length==2?2:1))continue;
            if((distance9(x,v)==1)!=(length==2))continue;
            mark(x,1);bridge.push_back(x);
            if(connect(x,v,length-1))return true;
            bridge.pop_back();mark(x,-1);
        }
        return false;
    }
    bool run(const Path& p,const vector<array<int,512>>& maps){
        const int n=int(p.size())-1;
        array<int,512> nearestSuffix;nearestSuffix.fill(-1);
        for(int j=0;j<=n;++j){
            nearestSuffix[p[j]]=j;
            for(int d=0;d<9;++d) nearestSuffix[p[j]^(1<<d)]=j;
        }
        for(int i=4;i+13<n;i+=stride){
            blocked.fill(0);occupied.fill(0);
            for(int t=0;t<=i;++t)mark(p[t],1);
            for(int a=0;a<(lead?9:1);++a){
                int anchor=lead?(p[i]^(1<<a)):p[i];
                if(lead){
                    if(occupied[anchor]||blocked[anchor]!=1)continue;
                    mark(anchor,1);
                }
            for(int skip=0;skip<=gap;++skip){
                int s=i+1+skip;
                for(const auto& transform:maps)for(int d=0;d<9;++d){
                    int start=anchor^(1<<d);
                    if(occupied[start]||blocked[start]!=1)continue;
                    int translation=start^transform[p[s]];
                    Path middle;int lastConflict=lead?nearestSuffix[anchor]:-1;
                    for(int j=s;j+5<=n;++j){
                        int x=translation^transform[p[j]];
                        if(occupied[x] || blocked[x]!=1)break;
                        mark(x,1);middle.push_back(x);lastConflict=max(lastConflict,nearestSuffix[x]);
                        if(j-s<7)continue;
                        ++geometries;
                        for(int drop=0;drop<=gap;++drop){
                            int k=j+1+drop, length=1+target-n+skip+drop-lead;
                            if(k+4>n||length<2||lastConflict>=k||distance9(x,p[k])>length)continue;
                            ++candidates;
                            for(int t=k;t<=n;++t)mark(p[t],1);
                            used=0;cut=false;bridge.clear();
                            if(connect(x,p[k],length)){
                                answer.assign(p.begin(),p.begin()+i+1);
                                if(lead)answer.push_back(anchor);
                                answer.insert(answer.end(),middle.begin(),middle.end());
                                answer.insert(answer.end(),bridge.begin(),bridge.end());
                                answer.insert(answer.end(),p.begin()+k,p.end());
                                if(int(answer.size())!=target+1||!snake(answer))abort();
                                return true;
                            }
                            cutoffs+=cut;
                            for(int t=k;t<=n;++t)mark(p[t],-1);
                        }
                    }
                    for(int v:middle)mark(v,-1);
                }
            }
                if(lead)mark(anchor,-1);
            }
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc<6 || argc>8)return 2;
    int target=stoi(argv[1]),trim=stoi(argv[2]),row=0;
    vector<array<int,512>> maps;
    for(int a=0;a<9;++a)for(int b=a;b<9;++b){
        if(a==b&&a!=0)continue;
        array<int,512> m;
        for(int x=0;x<512;++x)m[x]=x^(((((x>>a)^(x>>b))&1))?((1<<a)|(1<<b)):0);
        maps.push_back(m);
    }
    if(argc==8 && string(argv[7])=="cycles"){
        maps.clear();
        for(int a=0;a<9;++a)for(int b=a+1;b<9;++b)for(int c=b+1;c<9;++c){
            int mask=(1<<a)|(1<<b)|(1<<c);
            for(bool reverse:{false,true}){
                int second=reverse?c:b,third=reverse?b:c;
                array<int,512> perm{};
                for(int x=0;x<512;++x){
                    perm[x]=(x&~mask)|(((x>>a)&1)<<second)|(((x>>second)&1)<<third)|(((x>>third)&1)<<a);
                }
                maps.push_back(perm);
            }
        }
    }
    for(string w;cin>>w;++row){
        Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
        if(!snake(p))abort();
        for(int rev=0;rev<2;++rev){
            Path seed=p;if(rev)reverse(seed.begin(),seed.end());seed.resize(seed.size()-trim);
            Search f{target,stoi(argv[3]),stoi(argv[4]),stoi(argv[5]),argc>=7?stoi(argv[6]):0};
            bool hit=f.run(seed,maps);
            cout<<row<<" "<<rev<<" "<<hit<<" "<<f.geometries<<" "<<f.candidates<<" "<<f.nodes<<" "<<f.cutoffs;
            if(hit)for(int v:f.answer)cout<<" "<<v;
            cout<<endl;
            if(hit&&target>=192)return 0;
        }
    }
}
