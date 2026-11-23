#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
struct Candidate {int score;uint32_t tie;string w;bool operator<(const Candidate&o)const{return score!=o.score?score<o.score:tie<o.tie;}};
struct Retime {
 string grp;mt19937 rng;int depth,width,span;long long evaluated=0,expanded=0;int cnt[512],nb[512],path[220];
 Retime(int d,int b,int s,int seed):rng(seed),depth(d),width(b),span(s){}
 void upd(int v,int dir,int& cost){
    if(dir<0){cnt[v]--;cost-=cnt[v]+nb[v];}else{cost+=cnt[v]+nb[v];cnt[v]++;}
    for(int k=0;k<9;k++)nb[v^1<<k]+=dir;
 }
 int base(const string&w){
    fill(cnt,cnt+512,0);fill(nb,nb+512,0);int n=w.size(),cost=-n;path[0]=0;upd(0,1,cost);
    for(int i=0;i<n;i++){path[i+1]=path[i]^1<<(w[i]-'0');upd(path[i+1],1,cost);}return cost;
 }
 string run(const string&input,int&best){
    best=base(input);if(!best)return input;string record=input;int n=input.size();
    vector<Candidate> band{{best,0,input}};unordered_set<string>seen{input};
    for(int rep=0;rep<depth&&!band.empty();rep++){
       vector<Candidate> opts;
       for(auto&state:band){int cost=base(state.w);assert(cost==state.score);++expanded;
          array<int,220> hot{};array<int,512>head;head.fill(-1);array<int,220>prev;
          for(int j=0;j<=n;j++){int v=path[j];for(int d=-1;d<9;d++){int u=d<0?v:v^(1<<d);for(int i=head[u];i>=0;i=prev[i])if(j-i>1){hot[i]=hot[j]=1;}}prev[j]=head[v];head[v]=j;}
          int touched[221]={};for(int j=0;j<=n;j++)touched[j+1]=touched[j]+hot[j];
          for(int i=0;i<n;i++)for(int dir:{-1,1})for(int j=i+dir;j>=0&&j<n&&abs(j-i)<=span;j+=dir){
             if(grp[state.w[i]-'0']==grp[state.w[j]-'0'])break;
             int l=min(i,j),r=max(i,j);if(touched[r+1]==touched[l+1])continue;
             ++evaluated;array<int,64> mod;int v=path[l],val=cost;for(int h=l+1;h<=r;h++)upd(path[h],-1,val);
             for(int h=l;h<r;h++){char step=dir>0?state.w[h+1]:(h==l?state.w[r]:state.w[h-1]);v^=1<<(step-'0');mod[h-l]=v;upd(v,1,val);}
             if(val<=best+2){
                string w=state.w;if(dir>0)rotate(w.begin()+l,w.begin()+l+1,w.begin()+r+1);else rotate(w.begin()+l,w.begin()+r,w.begin()+r+1);
                if(seen.insert(w).second){if(val<best){best=val;record=w;if(!val)return w;}opts.push_back({val,rng(),move(w)});}
             }
             for(int h=l;h<r;h++)upd(mod[h-l],-1,val);for(int h=l+1;h<=r;h++)upd(path[h],1,val);assert(val==cost);
          }
       }
       if((int)opts.size()>width){nth_element(opts.begin(),opts.begin()+width,opts.end());opts.resize(width);}
       band=move(opts);
    }return record;
 }
};
int main(int argc,char**argv){if(argc!=9)return 2;ifstream in(argv[1]);ofstream out(argv[2]);Retime r(stoi(argv[3]),stoi(argv[4]),stoi(argv[5]),stoi(argv[7]));int take=stoi(argv[6]),clip=stoi(argv[8]);int row=0,wins=0,improved=0;string w,g;int l,n,h,m;
 while(row<take&&in>>w>>g>>l>>n>>h>>m){if(clip==1)w=w.substr(1);if(clip==2)w.pop_back();r.grp=g;int old=r.base(w),b;string z=r.run(w,b);assert(r.base(z)==b);if(b==0||b<old){out<<row<<' '<<old<<' '<<b<<' '<<z<<endl;improved+=b<old;wins+=b==0;}row++;if(!b&&z.size()>=192)break;}
 cout<<"rows "<<row<<" expanded "<<r.expanded<<" schedule_moves "<<r.evaluated<<" improved "<<improved<<" found "<<wins<<endl;
}
