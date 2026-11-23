#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <sstream>
#include <vector>
using namespace std;
using Bits=bitset<512>;
struct Search {
    Bits selected;
    array<Bits,512> hits;
    array<int,512> edges{};
    vector<int> points, basis;
    int target;
    uint64_t nodes=0,degree_ok=0,found=0;
    explicit Search(vector<int> p,int t): points(p),target(t) {
        for(int v:p)selected.set(v);
        for(int g=1;g<512;g++){
            for(int v:p)if(selected[v^g])hits[g].set(v);
            edges[g]=hits[g].count()/2;
        }
    }
    static bool extend_tips(vector<int>& p,int count,int other,bool turned,vector<int>& out){
        if(!count){
            if(turned){out=p;return true;}
            reverse(p.begin(),p.end());
            bool yes=extend_tips(p,other,0,true,out);
            reverse(p.begin(),p.end());return yes;
        }
        for(int a=0;a<9;a++){
            int y=p.back()^(1<<a);bool valid=true;
            for(size_t j=0;j+1<p.size();j++)if(__builtin_popcount((unsigned)(y^p[j]))<2){valid=false;break;}
            if(!valid)continue;
            p.push_back(y);bool yes=extend_tips(p,count-1,other,turned,out);p.pop_back();
            if(yes)return true;
        }return false;
    }
    bool inspect(int locked,int caseid){
        degree_ok++;
        array<int,512> coord;coord.fill(-1);coord[0]=0;
        vector<int> space{0};
        for(int i=0;i<9;i++){
            size_t n=space.size();for(size_t j=0;j<n;j++){int x=space[j]^basis[i];assert(coord[x]<0);coord[x]=coord[space[j]]^(1<<i);space.push_back(x);}
        }
        int tip=-1;
        for(int x:points){int n=0;for(int g:basis)n+=selected[x^g];if(n==1){tip=x;break;}}
        if(tip==-1)return false;
        vector<int> path;int prev=-1,x=tip;
        while(x!=-1){path.push_back(coord[x]);int next=-1;for(int g:basis){int y=x^g;if(y!=prev&&selected[y]){next=y;break;}}prev=x;x=next;}
        if(path.size()!=points.size())return false;
        if(getenv("Q9_LIST_WITNESSES")&&path.size()==192){
            string word;for(size_t j=1;j<path.size();j++)word.push_back('0'+__builtin_ctz((unsigned)(path[j]^path[j-1])));
            cout<<"PATH191 "<<caseid<<" "<<word<<endl;
        }
        int extra=target+1-(int)path.size();
        if(extra>0){
            vector<int> extended;
            for(int at_left=0;at_left<=extra&&extended.empty();at_left++){
                vector<int> copy=path;reverse(copy.begin(),copy.end());
                extend_tips(copy,at_left,extra-at_left,false,extended);
            }
            if(extended.empty())return false;
            path=extended;
        }
        if((int)path.size()-1<target)return false;
        cout<<"FOUND "<<caseid<<" locked "<<locked<<" basis";for(int z:basis)cout<<" "<<z;cout<<" path";for(int z:path)cout<<" "<<z;cout<<endl;found++;return true;
    }
    struct Entry{int g,proj;};
    bool descend(int locked,int id,const vector<Entry>& avail,int need,int left,const Bits& one,const Bits& two,uint64_t span){
        nodes++;
        if(!need){
            if(left==0&&one.count()==2&&(one|two)==selected)return inspect(locked,id);
            return false;
        }
        for(int i=0;i<(int)avail.size()-need+1;i++){
            auto [g,q]=avail[i];
            if((span>>q)&1u || edges[g]>left || (two&hits[g]).any())continue;
            Bits one2=one^hits[g],two2=two|(one&hits[g]);
            if(need==1 && (edges[g]!=left||one2.count()!=2))continue;
            uint64_t ext=0;
            for(uint64_t s=span;s;s&=s-1)ext|=uint64_t(1)<<(__builtin_ctzll(s)^q);
            vector<Entry> follow;
            if(need>1)for(int j=i+1;j<(int)avail.size();j++){
                auto e=avail[j];
                if(((span|ext)>>e.proj&1u)==0 && edges[e.g]<=left-edges[g] && !(two2&hits[e.g]).any())follow.push_back(e);
            }
            if((int)follow.size()<need-1)continue;
            basis.push_back(g);bool r=descend(locked,id,follow,need-1,left-edges[g],one2,two2,span|ext);basis.pop_back();if(r)return true;
        }return false;
    }
    bool run(int locked,int id){
        int missing=9-locked;assert(missing<=6);
        for(int mask=0;mask<512;mask++){
            if(__builtin_popcount((unsigned)mask)!=locked)continue;
            basis.clear();Bits one,two;int left=points.size()-1;bool ok=true;vector<int> other;
            for(int a=0;a<9;a++){int g=1<<a;if(!(mask&g)){other.push_back(a);continue;}
                if((two&hits[g]).any()){ok=false;break;}two|=one&hits[g];one^=hits[g];left-=edges[g];basis.push_back(g);}
            if(!ok||left<0)continue;
            vector<Entry> opts;
            for(int g=1;g<512;g++){if(!(g&(g-1)) || (hits[g]&two).any() || edges[g]>left)continue;int proj=0;for(int i=0;i<missing;i++)proj|=((g>>other[i])&1)<<i;
                if(proj)opts.push_back({g,proj});}
            sort(opts.begin(),opts.end(),[this](Entry a,Entry b){return edges[a.g]>edges[b.g];});
            if(descend(locked,id,opts,missing,left,one,two,1))return true;
        }return false;
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int goal=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);string line;int i=0;
    while(getline(cin,line)){
        vector<int> p;int x=0;if(line.rfind("points ",0)==0){istringstream in(line.substr(7));while(in>>x){if(x<0||x>=512)return 3;p.push_back(x);}}else{p.push_back(x);for(char c:line){if(c<'0'||c>'8')return 3;x^=1<<(c-'0');p.push_back(x);}}
        Bits uniq;for(int v:p)uniq.set(v);
        if(uniq.count()!=p.size()){cout<<"SKIP "<<i++<<endl;continue;}
        Search s(p,goal);for(int k=hi;k>=lo;k--)if(s.run(k,i))break;
        cout<<"END "<<i++<<" nodes "<<s.nodes<<" degree "<<s.degree_ok<<" found "<<s.found<<endl;
        if(s.found)break;
    }
    return 0;
}
