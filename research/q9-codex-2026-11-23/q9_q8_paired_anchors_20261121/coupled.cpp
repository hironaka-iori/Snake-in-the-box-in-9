#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cmath>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>
using namespace std;
struct Hint{int donor,at,axis;string word;};
struct Couple{int score,hi,mi;array<int,8> map;};
struct Walk{array<int,96> req,more;};
struct Eval{int cost,duplicates,blocked,start,len;string word;};
int geometry(const string &w){array<int,512> load{};int v=0;load[v]=1;int bad=0;for(char c:w){v^=1<<(c-'0');bad+=load[v]-1;for(int k=0;k<9;k++)bad+=load[v^(1<<k)];load[v]++;}return bad;}
Eval evaluate(const Walk& s,bool witness=false){
 array<int,512>cnt{},touch{};array<int,97>x{};array<int,96>p{},q{};int dup=0,bad=0,soft=0;
 auto add=[&](int v){dup+=cnt[v]++;for(int k=0;k<9;k++)touch[v^(1<<k)]++;};add(0);
 for(int i=0;i<96;i++){int a=1<<s.req[i],b=1<<s.more[i];p[i]=x[i]^a;q[i]=x[i]^b;x[i+1]=x[i]^a^b;add(x[i+1]);}
 int maxlen=0,st=0,chain=0;string w;
 for(int i=0;i<96;i++){int v=min(touch[p[i]],touch[q[i]]);bad+=v>2;soft+=v-2;
 if(v==2&&!dup){chain++;if(chain>maxlen){maxlen=chain;st=i-chain+1;}}else chain=0;
 if(witness){int a=s.req[i],b=s.more[i];if(touch[p[i]]>touch[q[i]])swap(a,b);w+=char('0'+a);w+=char('0'+b);}
 }return {40*dup+8*bad+soft,dup,bad,st,maxlen,w};
}
Couple match(const string &w,const string &m,int h,int mi){
 int count[9][10]={};for(int i=0;i<96;i++){int a=m[i]-'0'+1,x=w[2*i]-'0'+1,y=w[2*i+1]-'0'+1;count[a][x]--;if(x!=y)count[a][y]--;}
 int u[9]{},v[10]{},p[10]{},way[10]{};for(int i=1;i<=8;i++){p[0]=i;int j0=0,minv[10];fill(minv,minv+10,100000);bool done[10]{};
 do{done[j0]=true;int i0=p[j0],delta=10000,j1=0;for(int j=1;j<=9;j++)if(!done[j]){int c=count[i0][j]-u[i0]-v[j];if(c<minv[j]){minv[j]=c;way[j]=j0;}if(minv[j]<delta){delta=minv[j];j1=j;}}for(int j=0;j<=9;j++)if(done[j]){u[p[j]]+=delta;v[j]-=delta;}else minv[j]-=delta;j0=j1;}while(p[j0]);
 do{int j=way[j0];p[j0]=p[j];j0=j;}while(j0);}
 Couple c{0,h,mi,{}};for(int j=1;j<=9;j++)if(p[j]){c.map[p[j]-1]=j-1;c.score-=count[p[j]][j];}return c;
}
int main(int argc,char**argv){
 if(argc!=6)return 2;int nmatch=stoi(argv[1]),njobs=stoi(argv[2]),steps=stoi(argv[3]);mt19937 g(stoi(argv[4]));string pre=argv[5],w;ofstream out(pre+".tsv");ifstream ar("../q9_gap_generations/prior191.words"),ma("mothers.tsv");vector<string>mothers;vector<Hint> hints;int i,r,z,t,row=0;while(ma>>i>>r>>z>>t>>w)mothers.push_back(w);while(ar>>w){for(int p=0;p<=191;p++){for(int axis=0;axis<9;axis++){string s=w.substr(0,p)+char('0'+axis)+w.substr(p);if(geometry(s)<=2)hints.push_back({row,p,axis,s});}}++row;}
 vector<Couple> runs;for(int j=0;j<nmatch;j++){int h=g()%hints.size(),m=g()%mothers.size();runs.push_back(match(hints[h].word,mothers[m],h,m));}
 sort(runs.begin(),runs.end(),[](auto&a,auto&b){return a.score>b.score;});int best=999999,reach=0;long long moves=0;
 for(int j=0;j<njobs;j++){auto c=(j<njobs*3/4)?runs[j]:runs[g()%runs.size()];auto &h=hints[c.hi];auto &m=mothers[c.mi];Walk s;
 for(int k=0;k<96;k++){int a=c.map[m[k]-'0'],b=h.word[2*k]-'0',d=h.word[2*k+1]-'0';s.req[k]=a;s.more[k]=b==a?d:d==a?b:(g()%2?b:d);if(s.more[k]==a)s.more[k]=(a+1+g()%8)%9;}
 Eval cur=evaluate(s);int initial=cur.cost,bestlocal=cur.cost;Walk saved=s;int accepts=0;
 for(int it=0;it<steps;it++){
   int u=g()%96,v=(g()%5==0)?g()%96:clamp(u+int(g()%17)-8,0,95);if(u==v)continue;
   int x=s.more[u],y=s.more[v],a=x,b=y;int mode=g()%10;
   if(mode<=3){a=y;b=x;}else if(mode<=7){if(x!=y)continue;a=b=g()%9;}else{if(mode==8)v=u;b=a=g()%9;}
   if(a==s.req[u]||b==s.req[v]||(a==x&&b==y))continue;
   s.more[u]=a;s.more[v]=b;auto next=evaluate(s);++moves;float temp=1.5f+9.5f*(1.0f-(it%5000)/5000.f);
   if(next.cost<=cur.cost||g()%100000<100000*exp((cur.cost-next.cost)/temp)){cur=next;accepts++;if(cur.cost<bestlocal){saved=s;bestlocal=cur.cost;}}else{s.more[v]=y;s.more[u]=x;}
   if((it+1)%5000==0){s=saved;cur=evaluate(s);}if(!bestlocal)break;
 }
 Eval last=evaluate(saved,true);assert(last.cost==bestlocal);string mapping;for(int d:c.map)mapping+=char('0'+d);
 out<<j<<' '<<h.donor<<' '<<h.at<<' '<<h.axis<<' '<<c.mi<<' '<<mapping<<' '<<c.score<<' '<<initial<<' '<<last.cost<<' '<<last.duplicates<<' '<<last.blocked<<' '<<geometry(last.word)<<' '<<last.word<<endl;
 if(last.cost<best){best=last.cost;cerr<<"improved "<<j<<" energy "<<best<<" geometry "<<geometry(last.word)<<" distinct_even_pairs_colliding "<<last.duplicates<<" unavailable_midpoints "<<last.blocked<<endl;}if(!last.cost){reach++;assert(geometry(last.word)==0);break;}
 }
 cout<<"hints "<<hints.size()<<" sampled_alignments "<<runs.size()<<" max_axis_matches "<<runs.front().score<<" jobs_budget "<<njobs<<" anneal_steps_limit "<<steps<<" evaluated_moves "<<moves<<" best_energy "<<best<<" reached "<<reach<<endl;
}
