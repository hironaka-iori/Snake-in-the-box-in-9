#pragma once
#include <fstream>
#include <map>
struct HostCollection{
 std::set<std::string> known,completedHosts;
 std::ofstream paths,hosts;
 uint64_t placements=0,windows=0,newPaths=0;
 HostCollection(const char* base,const char* novel,const char* domains):paths(novel),hosts(domains){
    std::ifstream file(base);std::string w;
    if(!file||!paths||!hosts)abort();
    while(file>>w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));known.insert(shape(p));}
 }
 std::string shape(const Path& p){
    std::string best;
    for(int r=0;r<2;r++){
        int m[9],n=0;std::fill(m,m+9,-1);std::string w;
        for(int j=1;j<p.size();j++){
            int k=r?int(p.size())-j:j;int d=std::countr_zero(unsigned(p[k]^p[k-1]));
            if(m[d]<0)m[d]=n++;w+='0'+m[d];
        }
        if(!r||w<best)best=w;
    }return best;
 }
 void saveHost(const Path& whole){
    // Deduplicate labelled copies. The solver's coverage counting precedes this operation.
    Path sorted=whole;std::sort(sorted.begin(),sorted.end());std::string bits(64,0);
    for(int x:sorted)bits[x/8]=char((unsigned char)bits[x/8]|(1u<<(x%8)));
    if(completedHosts.insert(bits).second){for(int x:sorted)hosts<<x<<" ";hosts<<std::endl;}
 }
 bool record(const Path&p,const Path& host,bool& seen){
    windows++;if(!seen){saveHost(host);seen=true;placements++;}
    auto w=shape(p);if(!known.insert(w).second)return false;
    if(!valid(p,9)||p.size()!=192)abort();paths<<w<<std::endl;newPaths++;
    for(bool front:{false,true})for(int d=0;d<9;d++){
        int x=(front?p.front():p.back())^(1<<d);int touch=0;bool repeat=false;
        for(int y:p){repeat|=(x==y);touch+=std::popcount(unsigned(x^y))==1;}
        if(repeat||touch!=1)continue;auto q=p;if(front)q.insert(q.begin(),x);else q.push_back(x);
        if(!valid(q,9))abort();std::cout<<"FOUND 192";for(int v:q)std::cout<<" "<<v;std::cout<<std::endl;return true;
    }
    return false;
 }
 bool enumerate(Refill& r,int left,bool& seen){
    for(int x:r.vertices)if(r.used[x]){
        Path star{x};for(int d=0;d<9;d++)if(r.used[x^(1<<d)])star.push_back(x^(1<<d));
        if(star.size()<=3)continue;
        if(!left)return false;
        for(int y:star){r.used[y]=false;bool hit=enumerate(r,left-1,seen);r.used[y]=true;if(hit)return true;}
        return false;
    }
    std::array<bool,512> done{};
    for(int x:r.vertices)if(r.used[x]&&!done[x]){
        Path component{x};done[x]=true;int end=-1;
        for(int j=0;j<component.size();j++){int deg=0;for(int d=0;d<9;d++){
            int y=component[j]^(1<<d);if(!r.used[y])continue;deg++;if(!done[y]){done[y]=true;component.push_back(y);}
        }if(deg<2)end=component[j];}
        bool cycle=end<0;if(int(component.size())-int(cycle)<192)continue;
        Path ordered;int previous=-1,cur=cycle?x:end;
        for(int j=0;j<component.size();j++){
            ordered.push_back(cur);int next=-1;for(int d=0;d<9;d++){int y=cur^(1<<d);if(r.used[y]&&y!=previous){next=y;break;}}
            previous=cur;cur=next;
        }
        int len=ordered.size();if(cycle)ordered.insert(ordered.end(),component.size(),0);
        if(cycle)std::copy_n(ordered.begin(),len,ordered.begin()+len);
        for(int s=0;s<(cycle?len:len-191);s++){Path p(ordered.begin()+s,ordered.begin()+s+192);if(record(p,r.vertices,seen))return true;}
    }return false;
 }
};
