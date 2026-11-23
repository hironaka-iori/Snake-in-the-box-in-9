// Search length-preserving deformations in Q10. Score every folding that identifies two axes.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
using Path=vector<int>;using Hist=array<int,1024>;
bool valid(const Path& p,int dim){
    for(int i=0;i<int(p.size());i++){
        if(p[i]<0||p[i]>=(1<<dim))return false;
        for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));if(!d||((d==1)!=(j+1==i)))return false;}
    }return true;
}
Hist histogram(const Path& p){Hist h{};for(int i=0;i<int(p.size());i++)for(int j=0;j<i;j++)h[p[i]^p[j]]++;return h;}
struct Score{int best=100000,second=100000,mask=0,base=0;};
Score assess(const Hist& h,int edges){
    Score s;s.base=h[0]-edges;for(int bit=1;bit<1024;bit*=2)s.base+=h[bit];
    for(int a=1;a<1024;a*=2)for(int b=1;b<a;b*=2){
        int m=a|b,cost=s.base+h[m];
        for(int c=1;c<1024;c*=2)if(!(m&c))cost+=h[m|c];
        if(cost<s.best){s.second=s.best;s.best=cost;s.mask=m;}
        else s.second=min(s.second,cost);
    }return s;
}
Path fold(const Path& p,int m){
    int a=m&-m,b=m^a;Path q;
    for(int x:p){if(x&b)x^=m;q.push_back((x&(b-1))|((x/b/2)*b));}
    return q;
}
int defects(const Path& p){int v=0;for(int i=0;i<int(p.size());i++)for(int j=0;j<i-1;j++)v+=popcount(unsigned(p[i]^p[j]))<=1;return v;}
int main(int argc,char**argv){
    if(argc!=7)return 2;mt19937 rng(stoul(argv[1]));int runs=stoi(argv[2]),iterations=stoi(argv[3]),mode=stoi(argv[4]);
    ifstream input(argv[5]);ofstream proof(argv[6]);string line;vector<Path>bank;
    while(getline(input,line)){istringstream in(line);Path p;for(int x;in>>x;)p.push_back(x);if(p.size()==193)bank.push_back(p);}assert(!bank.empty());
    int global=10000,success=0;uint64_t moves=0,crossings=0;
    for(int r=0;r<runs;r++){
        int row=rng()%bank.size();Path orig=bank[row],p{0};int split=1<<(rng()%9);
        if(mode==1){for(int i=45;i>=10;i--)if(valid(Path(orig.begin(),orig.begin()+i+1),9)){orig.resize(i+1);break;}assert(valid(orig,9));}
        int n=orig.size(),edges=n-1;
        for(int i=1;i<n;i++){int d=orig[i]^orig[i-1];assert(has_single_bit(unsigned(d)));if(d==split&&rng()%2)d=512;p.push_back(p.back()^d);}
        if(mode==1){int i=1+rng()%(n-1),mask=1<<(rng()%10);int m=(p[i]^p[i-1])^mask;for(int k=i;k<n;k++)p[k]^=m;}
        Hist h=histogram(p);Score s=assess(h,edges);Path elite=p;int low=s.best;double coeff=.02+.01*(rng()%35),temp=.08+.015*(rng()%65);
        auto energy=[&](Score z){return z.best+coeff*min(25,z.second)+.28*z.base;};
        for(int it=0;it<=iterations;it++){
            if(mode==2||it==0){int m=0x3ff,minimum=100000;
                for(int a=1;a<1024;a*=2)for(int b=1;b<a;b*=2){m=a|b;int expected=s.base+h[m];for(int c=1;c<1024;c*=2)if(!(m&c))expected+=h[m|c];
                    int actual=defects(fold(p,m));assert(actual==expected);minimum=min(minimum,actual);}
                assert(minimum==s.best);}
            if(s.best<global){global=s.best;cout<<"BEST "<<r<<" "<<it<<" "<<row<<" "<<s.best<<" "<<s.second<<" "<<s.base<<" "<<s.mask;
                for(int x:p)cout<<" "<<x;cout<<endl;}
            if(!s.best&&mode!=2){Path q=fold(p,s.mask);assert(valid(q,9)&&valid(p,10));proof<<"FOUND "<<r<<" "<<it<<" "<<edges;for(int x:q)proof<<" "<<x;proof<<endl;++success;if(!mode)return 0;break;}
            if(it==iterations)break;
            if(it&&it%1100==0&&rng()%2){p=elite;h=histogram(p);s=assess(h,edges);}
            int start=1+rng()%edges,end=n,kind=rng()%10;int a=p[start]^p[start-1],b=1<<(rng()%10);
            if(kind<5){
                end=start+1+rng()%min(n-start,1+int(rng()%30));if(end<n){int last=p[end-1]^p[end];if(a!=last)b=last;}
            }else if(kind==5){end=start+1;if(end<n)b=p[end]^p[start];}
            else if(kind==6 && (a&s.mask))b=s.mask^a;
            if(a==b)continue;
            int m=a^b;if(end<n&&!has_single_bit(unsigned(p[end]^p[end-1]^m)))continue;
            Hist next=h;
            for(int i=start;i<end;i++){
                for(int j=0;j<start;j++){int z=p[i]^p[j];--next[z];++next[z^m];}
                for(int j=end;j<n;j++){int z=p[i]^p[j];--next[z];++next[z^m];}
            }
            Score q=assess(next,edges);++moves;
            double diff=energy(q)-energy(s),T=temp*(1.5-.95*(it%1100)/1100.);
            if(diff<=0||generate_canonical<double,32>(rng)<exp(-diff/T)){
                crossings+=q.mask!=s.mask;s=q;h=next;for(int i=start;i<end;i++)p[i]^=m;
                if(s.best<low||(s.best==low&&rng()%16==0)){low=s.best;elite=p;}
                if(mode==2)assert(h==histogram(p));
            }
        }
        if(r%10==9)cout<<"AT "<<r+1<<" "<<moves<<" "<<crossings<<" "<<success<<endl;
    }
    cout<<"DONE "<<runs<<" "<<moves<<" "<<crossings<<" "<<success<<endl;
}
