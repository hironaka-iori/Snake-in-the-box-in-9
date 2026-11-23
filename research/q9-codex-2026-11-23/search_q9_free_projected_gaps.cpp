#define Q9_FIBER_LIBRARY
#include "search_q9_three_axis_recolor.cpp"
#include <random>
#include <sstream>
struct Gap{int first,last;};
struct Bridge{
    Path& p; const vector<Gap>& gaps;
    int budget,nodes=0;array<int,512> used{},neighbors{};
    Bridge(Path& path,const vector<Gap>& holes,int cap):p(path),gaps(holes),budget(cap){
        for(int x:p)if(x>=0)mark(x,1);
    }
    void mark(int x,int d){used[x]+=d;for(int b=1;b<512;b*=2)neighbors[x^b]+=d;}
    int fill(int hole,int i){
        if(hole==gaps.size())return 1;
        if(++nodes>budget)return -1;
        const auto [a,b]=gaps[hole];int x=p[i],end=p[b],left=b-i;
        int hd=popcount(unsigned(x^end));
        if(hd>left||((hd^left)&1))return 0;
        if(left==1)return hd==1?fill(hole+1,hole+1==gaps.size()?0:gaps[hole+1].first):0;
        for(int bit=1;bit<512;bit*=2){
            int v=x^bit;
            if(used[v]||neighbors[v]!=(1+(left==2)))continue;
            if((popcount(unsigned(v^end))==1)!=(left==2))continue;
            mark(v,1);p[i+1]=v;int r=fill(hole,i+1);
            if(r==1)return 1;
            mark(v,-1);p[i+1]=-1;if(r<0)return -1;
        }
        return 0;
    }
};
struct Stats{uint64_t layouts=0,colorings=0,colorLimits=0,bridgeLimits=0,bridgeNodes=0;};
template<class Inspect>
bool enumerateColors(const Path& keep,const Path& times,int mask,int colorCap,Stats& stats,Inspect inspect){
    stats.layouts++;
    Fiber f(keep,mask,colorCap,times);if(!f.prepare())return false;
    int nodes=0;bool cutoff=false;
    auto dfs=[&](auto&& self,int left,int used)->bool{
        if(!left){
            stats.colorings++;Path q(keep.size());const int labels[]={0,3,5,6};
            for(int j=0;j<keep.size();j++){
                int z=labels[f.color[f.component[j]]]^(f.localParity[j]?7:0),k=0,x=f.base[j];
                for(int bit=1;bit<512;bit*=2)if(bit&mask){if(z&(1<<k))x|=bit;k++;}
                q[j]=x;
            }
            return inspect(q);
        }
        if(++nodes>colorCap){cutoff=true;return false;}
        int best=-1,score=-1,deny=0;
        for(int i=0;i<f.adj.size();i++)if(f.color[i]<0){
            int mask=0,open=0;for(int k:f.adj[i]){if(f.color[k]<0)open++;else mask|=1<<f.color[k];}
            if(mask==15)return false;int rating=256*popcount(unsigned(mask))+open;
            if(rating>score){score=rating;best=i;deny=mask;}
        }
        for(int c=0;c<min(4,used+1);c++)if(!(deny&(1<<c))){
            f.color[best]=c;if(self(self,left-1,max(used,c+1)))return true;f.color[best]=-1;
            if(cutoff)return false;
        }
        return false;
    };
    bool hit=dfs(dfs,f.adj.size(),0);stats.colorLimits+=cutoff;return hit;
}
bool search(const Path& parent,int mask,const vector<Gap>& gaps,int colorCap,int bridgeCap,Stats& stats,Path& answer){
    Path keep,times;for(int i=0;i<parent.size();i++){
        bool removed=false;for(auto [a,b]:gaps)removed|=(a<i&&i<b);
        if(!removed){keep.push_back(parent[i]);times.push_back(i);}
    }
    return enumerateColors(keep,times,mask,colorCap,stats,[&](const Path& colored){
        Path q(parent.size(),-1);for(int i=0;i<times.size();i++)q[times[i]]=colored[i];
        Bridge fill(q,gaps,bridgeCap);int r=fill.fill(0,gaps.front().first);
        stats.bridgeNodes+=fill.nodes;stats.bridgeLimits+=r<0;
        if(r!=1)return false;
        for(int i=0;i<q.size();i++){assert(q[i]>=0 && q[i]<512);for(int j=0;j<i;j++){
            int d=popcount(unsigned(q[i]^q[j]));assert(d && (d==1)==(i==j+1));
        }}
        answer=q;return true;
    });
}
#ifndef Q9_PROJECTED_GAP_LIBRARY
int main(int argc,char**argv){
    if(argc!=5)return 2;
    int runs=stoi(argv[1]),cc=stoi(argv[2]),bc=stoi(argv[3]);mt19937 rng(stoi(argv[4]));
    vector<int> masks;for(int m=1;m<512;m++)if(popcount(unsigned(m))==3)masks.push_back(m);
    string word;vector<Path> paths;vector<vector<pair<int,int>>> defects;
    while(cin>>word){Path p{0};for(char c:word)p.push_back(p.back()^(1<<(c-'0')));
        vector<pair<int,int>> bad;for(int i=0;i<p.size();i++)for(int j=0;j+1<i;j++)if(popcount(unsigned(p[i]^p[j]))==1)bad.emplace_back(i,j);
        paths.push_back(p);defects.push_back(bad);
    }
    Stats s;for(int run=0;run<runs;run++){
        int id=rng()%paths.size();auto &p=paths[id];auto &bad=defects[id];int n=p.size();
        vector<Gap> gaps;int count=1+(rng()%3!=0);
        for(int g=0;g<count;g++){
            int center=1+rng()%(n-2);
            if(!bad.empty() && (g<(int)bad.size() || rng()%2)){
                auto e=bad[(g+run)%bad.size()];center=rng()%2?e.first:e.second;
            }
            center=clamp(center,1,n-2);int width=2+rng()%17;
            int a=clamp(center-1-int(rng()%width),0,n-2-width);
            int b=a+width+1;if(center>=b){b=center+1;a=b-width-1;}
            gaps.push_back({a,b});
        }
        sort(gaps.begin(),gaps.end(),[](Gap a,Gap b){return a.first<b.first;});
        if(gaps.size()==2 && gaps[0].last>=gaps[1].first){gaps[0].last=max(gaps[0].last,gaps[1].last);gaps.pop_back();}
        int mask=masks[rng()%masks.size()];Path answer;
        if(search(p,mask,gaps,cc,bc,s,answer)){cout<<"FOUND "<<id<<" "<<mask<<" "<<answer.size()-1;for(int v:answer)cout<<" "<<v;cout<<endl;return 0;}
        if((run+1)%10000==0)cout<<"AT "<<s.layouts<<" "<<s.colorings<<" "<<s.colorLimits<<" "<<s.bridgeLimits<<" "<<s.bridgeNodes<<endl;
    }
    cout<<"DONE "<<s.layouts<<" "<<s.colorings<<" "<<s.colorLimits<<" "<<s.bridgeLimits<<" "<<s.bridgeNodes<<endl;
}

#endif
