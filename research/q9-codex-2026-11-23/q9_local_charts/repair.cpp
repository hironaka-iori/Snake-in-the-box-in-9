#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using Word=uint64_t;
using Path=vector<int>;
int distance9(int x,int y){return popcount(unsigned(x^y));}
bool valid(const Path& p){
    for(int j=0;j<int(p.size());++j)for(int i=0;i<j;i++){
        int d=distance9(p[i],p[j]);if(!d||((d==1)!=(i+1==j)))return false;
    }return true;
}
struct Domain{Path values;array<Word,512> halo{},adj{};};
struct Solver{
    const vector<Domain>& vars;int limit,visited=0;Path result;
    Word compatible(int j,int x,int gap)const{return gap==1?vars[j].adj[x]:~vars[j].halo[x];}
    bool propagate(vector<Word>& dom,Path queue){
        vector<bool> pending(dom.size());for(int i:queue)pending[i]=true;
        for(size_t step=0;step<queue.size();step++){
            int i=queue[step];pending[i]=false;bool fixed=has_single_bit(dom[i]);
            int first=fixed?0:max(0,i-1),last=fixed?int(dom.size()):min(int(dom.size()),i+2);
            for(int j=first;j<last;j++)if(i!=j){
                Word support=0;int gap=abs(i-j);
                for(Word mask=dom[i];mask;mask&=mask-1){
                    support|=compatible(j,vars[i].values[countr_zero(mask)],gap);
                    if((support&dom[j])==dom[j])break;
                }
                Word rest=dom[j]&support;if(rest==dom[j])continue;
                if(!rest)return false;dom[j]=rest;
                if(!pending[j]){queue.push_back(j);pending[j]=true;}
            }
        }
        return true;
    }
    int search(vector<Word>& dom,Path queue){
        if(++visited>limit)return -1;
        if(!propagate(dom,queue))return 0;
        Path preferred(dom.size()),count(dom.size());
        array<Path,512> at;
        for(int i=0;i<int(dom.size());i++){
            int x=vars[i].values[countr_zero(dom[i])];preferred[i]=x;
            if(i&&distance9(preferred[i-1],x)!=1){count[i]+=2;count[i-1]+=2;}
            for(int bit=0;bit<=9;bit++){
                int y=bit==9?x:x^(1<<bit);
                for(int j:at[y])if(i-j>1){count[i]++;count[j]++;}
            }
            at[x].push_back(i);
        }
        int branch=-1;double best=0;
        for(int i=0;i<int(dom.size());i++)if(count[i]&&popcount(dom[i])>1){
            double rank=double(count[i])/popcount(dom[i]);if(rank>best){best=rank;branch=i;}
        }
        if(branch<0){assert(valid(preferred));result=preferred;return 1;}
        Word bit=dom[branch]&-dom[branch];auto next=dom;
        next[branch]=bit;int v=search(next,{branch});if(v)return v;
        dom[branch]^=bit;return search(dom,{branch});
    }
};
Domain build(Path vals){
    Domain out;out.values=vals;assert(!vals.empty()&&vals.size()<=63);
    for(int k=0;k<int(vals.size());k++){
        int x=vals[k];Word bit=Word(1)<<k;out.halo[x]|=bit;
        for(int d=0;d<9;d++){int y=x^(1<<d);out.halo[y]|=bit;out.adj[y]|=bit;}
    }return out;
}
bool brute(const vector<Domain>& d,Path& p){
    int i=p.size();if(i==int(d.size()))return true;
    for(int x:d[i].values){p.push_back(x);if(valid(p)&&brute(d,p))return true;p.pop_back();}
    return false;
}
int solve(const vector<Domain>& d,Solver& s){
    vector<Word> masks;for(const auto& a:d)masks.push_back((Word(1)<<a.values.size())-1);
    Path q(d.size());iota(q.begin(),q.end(),0);return s.search(masks,q);
}
int main(int argc,char** argv){
    if(argc!=7)return 2;
    mt19937 rng(stoul(argv[1]));int runs=stoi(argv[2]),budget=stoi(argv[3]),mode=stoi(argv[4]),dim=stoi(argv[5]);ifstream f(argv[6]);
    vector<Path> bank;string line;
    if(mode!=2)while(getline(f,line)){istringstream in(line);Path p;for(int x;in>>x;)p.push_back(x);if(p.size()>=190)bank.push_back(p);}
    if(mode!=2)assert(bank.size());
    int yes=0,no=0,unknown=0;long long nodes=0;
    for(int r=0;r<runs;r++){
        int row=0;vector<Domain> vars;Path source,truth;
        if(mode==2){
            int n=4+rng()%7;for(int i=0;i<n;i++){
                Path vals;for(int j=0;j<16;j++)if(int(popcount(unsigned(j))%2)==i%2&&rng()%3==0)vals.push_back(j);
                if(vals.empty())vals.push_back(i%2);shuffle(vals.begin(),vals.end(),rng);vars.push_back(build(vals));
            }
        }else{
            row=rng()%bank.size();source=bank[row];if(rng()%2)reverse(source.begin(),source.end());
            if(mode==1){
                // Extract a verified contiguous path and center a few local domains on wrong vertices.
                int k=(r%3==0)?91:53;
                bool ok=false;
                for(int t=0;t+k<=int(source.size());t++){Path piece(source.begin()+t,source.begin()+t+k);
                    if(valid(piece)){source=piece;ok=true;break;}}
                assert(ok);truth=source;
            }
            int mask=0,until=0,prev=0,style=r%4;
            for(int i=0;i<int(source.size());i++){
                if(i>=until){prev=mask;mask=0;if(style==2&&prev){int x=prev;while(x&&popcount(unsigned(mask))<dim-2){
                    int b=1<<(rng()%9);if(x&b){x^=b;mask|=b;}}}
                    while(popcount(unsigned(mask))<dim)mask|=1<<(rng()%9);
                    until=i+2+rng()%(style==0?6:style==1?20:40);}
                Path vals{source[i]};
                for(int sub=mask;sub;sub=(sub-1)&mask)
                    if(!(popcount(unsigned(sub))%2))vals.push_back(source[i]^sub);
                shuffle(vals.begin()+1,vals.end(),rng);
                if(mode==1&&i%9==3){swap(vals[0],vals[1]);source[i]=vals[0];}
                vars.push_back(build(vals));
            }
        }
        Solver s{vars,budget};int v=solve(vars,s);nodes+=s.visited;
        if(mode==2){Path p;bool hit=brute(vars,p);assert(v>=0 && (v==1)==hit);}
        if(mode==1){assert(!valid(source)&&valid(truth));assert(v!=0);}
        if(v==1){
            yes++;assert(valid(s.result));
            cout<<"FOUND "<<r<<" "<<row<<" "<<s.result.size()-1;for(int x:s.result)cout<<" "<<x;cout<<endl;
            if(mode==0)return 0;
        }else if(v==0)no++;else unknown++;
        if(r%25==24)cout<<"AT "<<r+1<<" "<<yes<<" "<<no<<" "<<unknown<<" "<<nodes<<endl;
    }
    cout<<"DONE "<<runs<<" "<<yes<<" "<<no<<" "<<unknown<<" "<<nodes<<endl;
}
