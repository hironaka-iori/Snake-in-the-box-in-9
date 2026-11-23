// Random walks on ordered same-color anchors. Intermediate odd vertices are
// reselected globally at every score evaluation.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cmath>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using P=vector<int>;
struct Score {int debt,pairs;};
Score score(const P& p, P* full=nullptr){
    array<unsigned char,512> load{},seen{};
    int duplicates=0;
    for(int v:p){duplicates+=seen[v]++!=0;for(int bit=1;bit<512;bit*=2)++load[v^bit];}
    int debt=0,blocked=0;if(full)*full={p[0]};
    for(int i=1;i<int(p.size());i++){
        int x=p[i-1],y=p[i],mask=x^y;
        assert(popcount(unsigned(mask))==2);
        int a=x^(mask&-mask),b=y^(mask&-mask);
        if(load[b]<load[a])swap(a,b);
        debt+=load[a]-2;blocked+=load[a]>2;
        if(full){full->push_back(a);full->push_back(y);}
    }
    return {debt+8*duplicates,blocked};
}
void verify(const P& w){
    for(int j=0;j<int(w.size());j++)for(int i=0;i<j;i++)
        assert(w[j]!=w[i] && ((popcount(unsigned(w[j]^w[i]))==1)==(i+1==j)));
}
int main(int argc,char** argv){
    if(argc!=7)return 2;
    mt19937 rng(stoul(argv[1]));int trials=stoi(argv[2]),steps=stoi(argv[3]),control=stoi(argv[4]);
    vector<P> bank;string s;ifstream hybrids(argv[5]),archive(argv[6]);
    if(!control)while(getline(hybrids,s)){istringstream line(s);P p;int i=0;for(int x;line>>x;i++)if(i%2==0)p.push_back(x);bank.push_back(p);}
    while(archive>>s)for(int r=0;r<2;r++){
        reverse(s.begin(),s.end());int v=0;P p{0};
        for(int i=0;i<int(s.size());i++){v^=1<<(s[i]-'0');if(i%2)p.push_back(v);}
        if(control){bank.push_back(p);continue;}
        int last=1<<(s.back()-'0');
        for(int b=1;b<512;b*=2)if(b!=last){p.push_back(v^b);if(score(p).debt<=8)bank.push_back(p);p.pop_back();}
    }
    assert(!bank.empty());
    int best=10000,success=0;uint64_t proposals=0,accepted=0;
    for(int trial=0;trial<trials;trial++){
        P p=bank[rng()%bank.size()];const int end=p.size()-1;
        if(control){
            bool damaged=false;
            for(int t=0;t<300&&!damaged;t++){
                int i=1+rng()%(end-1),x=p[i-1],y=p[i+1];P opts;
                for(int a=1;a<512;a*=2)for(int b=1;b<a;b*=2){
                    int q=x^a^b;if(q!=p[i]&&popcount(unsigned(q^y))==2)opts.push_back(q);}
                if(opts.empty())continue;
                int old=p[i];p[i]=opts[rng()%opts.size()];
                if(score(p).debt>0)damaged=true;else p[i]=old;
            }
            assert(damaged);
        }
        Score now=score(p);P elite=p;int low=now.debt;double base=.25+.01*(rng()%145);
        for(int it=0;it<steps;it++){
            if(it&&it%1900==0&&rng()%3){p=elite;now=score(p);}
            P q=p;unsigned kind=rng()%10;
            if(kind<5){
                int i=rng()%(end+1),x=i?p[i-1]:p[1];
                P opts;for(int a=1;a<512;a*=2)for(int b=1;b<a;b*=2){
                    int v=x^a^b;
                    if(v!=p[i] && (!i||i==end||popcount(unsigned(v^p[i+1]))==2))opts.push_back(v);}
                if(opts.empty())continue;q[i]=opts[rng()%opts.size()];
            }else{
                int width=2+rng()%min(end-1,kind>=8?60:10);
                int start=rng()%(end-width+1),stop=start+width,m=p[start]^p[stop];
                if(kind==9){for(int i=start+1;i<stop;i++)q[i]=m^p[stop+start-i];}
                else{
                    int a=1<<(rng()%9),b=1<<(rng()%9);
                    if(a==b||bool(m&a)!=bool(m&b))continue;
                    for(int i=start+1;i<stop;i++){int z=p[i]^p[start];if(bool(z&a)!=bool(z&b))q[i]^=a|b;}
                }
            }
            if(p==q)continue;++proposals;
            Score next=score(q);
            if(next.debt<best){best=next.debt;cout<<"BEST "<<trial<<" "<<it<<" debt "<<best<<" blocked "<<next.pairs<<" anchors";for(int v:q)cout<<" "<<v;cout<<endl;}
            if(!next.debt){P w;score(q,&w);verify(w);++success;
                cout<<"FOUND "<<trial<<" "<<it<<" "<<w.size()-1;for(int v:w)cout<<" "<<v;cout<<endl;
                if(!control)return 0;break;}
            double T=base*(1.65-1.35*(it%1900)/1900.);
            if(next.debt<=now.debt||generate_canonical<double,32>(rng)<exp((now.debt-next.debt)/T)){
                p.swap(q);now=next;++accepted;
                if(now.debt<low || (now.debt==low&&rng()%7==0)){low=now.debt;elite=p;}
            }
        }
        if(trial%10==9)cout<<"AT "<<trial+1<<" "<<proposals<<" "<<accepted<<" "<<success<<endl;
    }
    cout<<"DONE "<<trials<<" "<<proposals<<" "<<accepted<<" "<<success<<endl;
}
