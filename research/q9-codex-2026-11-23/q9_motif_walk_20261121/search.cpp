#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using Seq=vector<int>;
string form(const Seq& s){
    array<int,9> label; label.fill(-1);
    int n=0;string out;
    for(int x:s){if(label[x]<0)label[x]=n++;out+=char('0'+label[x]);}
    return out;
}
string canonical(Seq s){string f=form(s);reverse(s.begin(),s.end());return min(f,form(s));}
bool independent_check(const Seq& s){
    Seq p={0}; for(int d:s)p.push_back(p.back()^(1<<d));
    for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){
        int h=popcount(unsigned(p[i]^p[j]));
        if(h==0 || ((h==1)!=(i==j+1)))return false;
    }
    return true;
}
int k, free_from, best=0;
long long rootlimit, calls=0, local=0, truncated=0, roots_done=0, records=0;
unordered_map<uint64_t,unsigned> masks;
set<string> parents, discovered;
mt19937_64 rng;
Seq s; array<int,512> block{};
uint64_t context(const Seq& seq,size_t end,array<int,9>& rank,int& next){
    rank.fill(-1);next=0;
    uint64_t key=0;
    for(size_t j=end-k;j<end;j++){
        int& r=rank[seq[j]];
        if(r<0)r=next++;
        key=key*16+r;
    }
    return key;
}
void mark(int x,int sign){block[x]+=sign;for(int d=0;d<9;d++)block[x^(1<<d)]+=sign;}
void search(int x){
    if(local>=rootlimit)return;
    calls++;local++;
    int n=s.size();best=max(best,n);
    if(n>=191){
        if(n==191)records++;
        else {
            if(!independent_check(s))abort();
            cout<<"FOUND "<<n<<" "<<form(s)<<endl;exit(0);
        }
        auto c=canonical(s);
        if(!parents.contains(c) && discovered.insert(c).second){
            if(!independent_check(s))abort();
            if(discovered.size()<=3)cout<<"NEW191 "<<c<<"\n";
        }
    }
    unsigned choices=511;
    if(n<free_from){
        array<int,9> rank;int next;
        auto found=masks.find(context(s,n,rank,next));
        if(found==masks.end())return;
        choices=0;
        for(int d=0;d<9;d++)if(found->second&(1u<<(rank[d]<0?next:rank[d])))choices|=1u<<d;
    }
    int rotate_by=rng()%9;
    for(int j=0;j<9;j++){
        int d=(j+rotate_by)%9,y=x^(1<<d);
        if((choices&(1u<<d)) && !block[y]){
            mark(x,1);s.push_back(d);search(y);s.pop_back();mark(x,-1);
            if(local>=rootlimit)return;
        }
    }
}
int main(int argc,char** argv){
    if(argc!=7)return 2;
    k=stoi(argv[2]);int prefix=stoi(argv[3]);free_from=stoi(argv[4]);rootlimit=stoll(argv[5]);rng.seed(stoull(argv[6]));
    if(k<1||k>16||prefix<k||free_from>192||prefix>190)return 2;
    ifstream f(argv[1]);string raw;vector<Seq> bank;set<string> roots;
    while(f>>raw){
        Seq q;for(char c:raw){if(c<'0'||c>'8')return 3;q.push_back(c-'0');}
        if(q.size()!=191)return 3;
        if(independent_check(q))parents.insert(canonical(q));
        for(int side=0;side<2;side++,reverse(q.begin(),q.end())){
            bank.push_back(q);
            Seq start(q.begin(),q.begin()+prefix);
            if(independent_check(start))roots.insert(form(start));
        }
    }
    if(bank.empty())return 3;
    for(auto& q:bank)for(int i=k;i<(int)q.size();i++){
        array<int,9> rank;int next;auto key=context(q,i,rank,next);
        int r=rank[q[i]];masks[key]|=1u<<(r<0?next:r);
    }
    vector<string> ordered(roots.begin(),roots.end());shuffle(ordered.begin(),ordered.end(),rng);
    for(auto& root:ordered){
        s.clear();block.fill(0);int x=0;
        for(char c:root){int d=c-'0';mark(x,1);x^=1<<d;s.push_back(d);}
        local=0;search(x);roots_done++;truncated+=(local>=rootlimit);
    }
    cout<<"source_words "<<bank.size()/2<<" parents "<<parents.size()<<" contexts "<<masks.size()<<" roots "<<roots_done<<" truncated "<<truncated
        <<" nodes "<<calls<<" best_edges "<<best<<" visits191 "<<records<<" new191classes "<<discovered.size()<<endl;
    return 0;
}
