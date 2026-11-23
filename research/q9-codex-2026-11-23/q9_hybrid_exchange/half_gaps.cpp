// Replace several windows in the even-index subsequence. All odd vertices, including those
// outside the windows, are selected only after their two even neighbors have been fixed.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;
struct Env{
    array<uint8_t,256> loads{},forbid{};
    array<int16_t,256> alt;
    Env(){alt.fill(-1);}
    void lock(int odd){for(int b=1;b<512;b*=2)forbid[(odd^b)>>1]=1;}
    bool add(int x){if(forbid[x>>1])return false;forbid[x>>1]=1;
        for(int b=1;b<512;b*=2){int y=(x^b)>>1;
            if(loads[y]++==2&&alt[y]>=0){int w=alt[y];alt[y]=alt[w>>1]=-1;lock(w);}}
        return true;
    }
    bool edge(int x,int y){
        int m=x^y;if(popcount(unsigned(m))!=2)return false;int a=x^(m&-m),b=y^(m&-m);
        bool l=loads[a>>1]==2,r=loads[b>>1]==2;
        if(!l&&!r)return false;
        if(l&&r){alt[a>>1]=b;alt[b>>1]=a;}else lock(l?a:b);
        return true;
    }
};
struct Job{
    P seed,q,solution;vector<P> gaps;int cap,visits=0;bool limited=false;mt19937& rng;
    Job(P p,int n,mt19937& r):seed(p),q(p),cap(n),rng(r){}
    bool finish(const Env& h){P w{q[0]};
        for(int i=1;i<int(q.size());i++){int x=q[i-1],y=q[i],m=x^y;assert(popcount(unsigned(m))==2);
            int a=x^(m&-m),b=y^(m&-m),v=h.loads[a>>1]==2?a:b;assert(h.loads[v>>1]==2);w.push_back(v);w.push_back(y);}
        for(int j=0;j<int(w.size());j++)for(int i=0;i<j;i++)assert(w[i]!=w[j]&&((popcount(unsigned(w[i]^w[j]))==1)==(i+1==j)));
        solution=w;return true;
    }
    bool dfs(Env& env,int g,int at){
        if(g==int(gaps.size()))return finish(env);
        if(++visits>cap){limited=true;return false;}
        auto& hole=gaps[g];int dir=(hole.back()==0?-1:1);
        if(at==int(hole.size())){
            int end=hole.back()+dir;
            if(end>=0&&end<int(q.size())&&!env.edge(q[hole.back()],q[end]))return false;
            return dfs(env,g+1,0);
        }
        int i=hole[at],from=q[i-dir],end=hole.back()+dir;
        array<int,36> moves;int n=0;
        for(int a=1;a<512;a*=2)for(int b=1;b<a;b*=2){int x=from^a^b;
            if(env.forbid[x>>1])continue;
            if(env.loads[(from^a)>>1]!=1&&env.loads[(from^b)>>1]!=1)continue;
            if(end>=0&&end<int(q.size())){
                int dist=popcount(unsigned(x^q[end])),remain=hole.size()-at;
                if(dist>2*remain||(remain==1&&dist!=2))continue;
            }
            moves[n++]=x;
        }
        shuffle(moves.begin(),moves.begin()+n,rng);
        for(int k=0;k<n;k++){int x=moves[k];Env next=env;if(!next.add(x)||!next.edge(from,x))continue;
            q[i]=x;if(dfs(next,g,at+1))return true;if(limited)break;
        }return false;
    }
    bool run(const P& release){
        Env h;vector<bool> free(q.size());for(int i:release)free.at(i)=true;
        for(int i=0;i<int(q.size());i++)if(!free[i]&&!h.add(q[i]))return false;
        for(int i=1;i<int(q.size());i++)if(!free[i]&&!free[i-1]&&!h.edge(q[i-1],q[i]))return false;
        for(int i=0;i<int(q.size());)if(free[i]){
            P z;while(i<int(q.size())&&free[i])z.push_back(i++);
            if(z[0]==0){if(z.size()==q.size())return false;reverse(z.begin(),z.end());}
            gaps.push_back(z);
        }else i++;
        sort(gaps.begin(),gaps.end(),[](const P& a,const P& b){return a.size()<b.size();});
        return dfs(h,0,0);
    }
};
int main(int argc,char**argv){
 if(argc!=5)return 2;mt19937 rng(stoul(argv[1]));int runs=stoi(argv[2]),limit=stoi(argv[3]),control=stoi(argv[4]);vector<P> bank;string s;
 while(getline(cin,s)){istringstream in(s);P p;for(int v;in>>v;)p.push_back(v);if(!p.empty())bank.push_back(p);}
 uint64_t entered=0,cut=0,nodes=0,success=0;int best=0;
 for(int it=0;it<runs;it++){
    int row=rng()%bank.size();P source=bank[row];if(rng()%2)reverse(source.begin(),source.end());P p;
    for(int i=0;i<int(source.size());i+=2)p.push_back(source[i]);
    // Work in the even chart; translating every point preserves distances.
    if(popcount(unsigned(p[0]))%2)for(int& v:p)v^=1;
    int n=p.size();vector<P> obligations;
    for(int i=1;i<n;i++){int m=p[i]^p[i-1];if(popcount(unsigned(m))!=2)continue;
        int a=p[i-1]^(m&-m),b=p[i]^(m&-m);P x,y;
        for(int j=0;j<n;j++)if(j!=i&&j+1!=i){if(popcount(unsigned(p[j]^a))==1)x.push_back(j);if(popcount(unsigned(p[j]^b))==1)y.push_back(j);}
        if(!x.empty()&&!y.empty()){
            int mode=rng()%4;if(mode==0)obligations.push_back(x);else if(mode==1)obligations.push_back(y);else obligations.push_back({mode==2?i:i-1});
        }
    }
    P release;
    auto window=[&](int i,int w){int off=rng()%w;for(int t=max(0,i-off);t<min(n,i+w-off);t++)release.push_back(t);};
    for(auto& o:obligations)for(int j:o)window(j,1+rng()%(control?3:13));
    int extra=control?2:1+rng()%4;for(int j=0;j<extra;j++)window(rng()%n,2+rng()%(control?3:12));
    if(!control&&rng()%2)window(rng()%2?n-1:0,2+rng()%15);
    Job job(p,limit,rng);bool hit=job.run(release);entered+=job.visits>0;cut+=job.limited;nodes+=job.visits;
    if(hit){int len=job.solution.size()-1;success++;
        if(len>best){best=len;cout<<"FOUND "<<row<<" "<<it<<" "<<len;for(int v:job.solution)cout<<" "<<v;cout<<endl;}
        if(!control&&len>=192)return 0;}
    if(it%1000==999)cout<<"AT "<<it+1<<" "<<entered<<" "<<cut<<" "<<nodes<<" "<<success<<endl;
 }cout<<"DONE "<<runs<<" "<<entered<<" "<<cut<<" "<<nodes<<" "<<success<<endl;
}
