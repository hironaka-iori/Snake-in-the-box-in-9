#define main old_cli
#include "../search_q9_fiber_anneal.cpp"
#undef main
#include <set>
#include <map>
struct Seg{int c,s,t;M m;};
using Segs=vector<Seg>;
int dist(int x,int y){return popcount(unsigned(x^y));}
int penalty(const Seg&a,const Seg&b,bool consecutive){
 int d=dist(a.c,b.c);if(d>=2)return 0;
 if(d==1)return popcount(a.m&b.m)-int(consecutive);
 if(consecutive)abort();
 int score=2*popcount(a.m&b.m);
 static M low[5]={0x55555555,0x33333333,0x0f0f0f0f,0x00ff00ff,0x0000ffff};
 for(int k=0;k<5;++k){int h=1<<k;score+=popcount(((((a.m&low[k])<<h)|((a.m>>h)&low[k]))&b.m));}
 return score;
}
pair<int,int> stats(const Segs&v){
 int n=0,b=0;for(int i=0;i<v.size();++i){n+=popcount(v[i].m);for(int j=0;j<i;++j)b+=penalty(v[i],v[j],i==j+1);}return {n,b};
}
vector<int> flat(const Segs&v){
 vector<int> p;for(auto&a:v){int x=a.s;M rest=a.m;
  while(true){p.push_back(32*a.c+x);rest^=1u<<x;if(!rest)break;M next=nb[x]&rest;if(popcount(next)!=1)abort();x=countr_zero(next);}
  if(x!=a.t)abort();
 }return p;
}
bool valid(const vector<int>&p){
 for(int i=0;i<p.size();++i)for(int j=0;j<i;++j)if(p[i]==p[j]||(dist(p[i],p[j])==1)!=(j+1==i))return false;return true;
}
Segs parts(const vector<int>&p){
 Segs v;
 for(int x:p){int c=x/32,t=x%32;if(v.empty()||v.back().c!=c)v.push_back({c,t,t,0});v.back().t=t;v.back().m|=1u<<t;}return v;
}
int local(const Segs&v,int i){
 int b=0;for(int j=0;j<v.size();++j)if(i!=j)b+=penalty(v[i],v[j],abs(i-j)==1);return b;
}
bool mutate(Segs&v,int kind,double fee){
 int n=v.size(),i=pick(n);
 if(kind<5){
  if(kind==0&&i==0)v[i].s=pick(32);if(kind==1&&i==n-1)v[i].t=pick(32);
  auto&o=opts[v[i].s][v[i].t];M best=0;double top=-1e8;
  for(int h=0;h<10;++h){v[i].m=o[pick(o.size())];double s=popcount(v[i].m)-fee*local(v,i)+pick(100)/150.;if(s>top){top=s;best=v[i].m;}}
  v[i].m=best;return true;
 }
 if(kind<8){
  i=pick(n-1);int p=v[i].t^(1<<pick(5));if(pick(3)==0)p=pick(32);
  v[i].t=v[i+1].s=p;
  auto&a=opts[v[i].s][p];auto&b=opts[p][v[i+1].t];
  double top=-1e8;M x=0,y=0;
  for(int h=0;h<12;++h){v[i].m=a[pick(a.size())];v[i+1].m=b[pick(b.size())];
   double s=popcount(v[i].m)+popcount(v[i+1].m)-fee*(local(v,i)+local(v,i+1)-penalty(v[i],v[i+1],true))+pick(100)/150.;
   if(s>top){top=s;x=v[i].m;y=v[i+1].m;}}
  v[i].m=x;v[i+1].m=y;return true;
 }
 if(kind==8 || kind==9){
  int j=kind==8?i:min(n-1,i+pick(6)+1);vector<int> moves;
  for(int z=1;z<16;++z)if((i==0||dist(v[i].c^z,v[i-1].c)==1)&&(j==n-1||dist(v[j].c^z,v[j+1].c)==1))moves.push_back(z);
  if(moves.empty())return false;int z=moves[pick(moves.size())];for(int h=i;h<=j;++h)v[h].c^=z;return true;
 }
 if(kind==10){
  int j=min(n-1,i+pick(8));int a=pick(5),b=pick(5);if(a==b)return false;
  int anchor=v[i].s,e=v[j].t;
  auto tr=[&](int x){int u=x^anchor;return (((u>>a)^(u>>b))&1)?x^(1<<a)^(1<<b):x;};
  if(tr(e)!=e)return false;
  for(int h=i;h<=j;++h){M m=0;for(M t=v[h].m;t;t&=t-1)m|=1u<<tr(countr_zero(t));v[h].m=m;v[h].s=tr(v[h].s);v[h].t=tr(v[h].t);}return true;
 }
 if(kind==11){
  if(n>=31||popcount(v[i].m)<3)return false;
  auto q=flat({v[i]});int h=pick(q.size()-2),j=h+2+pick(q.size()-h-2),c=v[i].c^(1<<pick(4));vector<int> path;
  for(int k=0;k<=h;++k)path.push_back(q[k]);
  for(int k=h;k<=j;++k)path.push_back(32*c+q[k]%32);
  for(int k=j;k<q.size();++k)path.push_back(q[k]);
  auto three=parts(path);v.erase(v.begin()+i);v.insert(v.begin()+i,three.begin(),three.end());return true;
 }
 if(kind==12){
  vector<int> pos;for(int j=0;j+2<n;++j)if(v[j].c==v[j+2].c)pos.push_back(j);
  if(pos.empty())return false;i=pos[pick(pos.size())];Seg both{v[i].c,v[i].s,v[i+2].t,0};
  auto& o=opts[both.s][both.t];M wanted=v[i].m|v[i+1].m|v[i+2].m;int best=999;
  for(int t=0;t<15;++t){M m=o[pick(o.size())];int dif=popcount(m^wanted);if(dif<best){best=dif;both.m=m;}}
  v.erase(v.begin()+i,v.begin()+i+3);v.insert(v.begin()+i,both);return true;
 }
 return false;
}
int main(int argc,char**argv){
 int steps=stoi(argv[1]),goal=stoi(argv[2]);rng.seed(stoul(argv[3]));
 for(int v=0;v<32;v++)for(int d=0;d<5;d++)nb[v]|=1u<<(v^(1<<d));for(int v=0;v<32;v++)gen(v,v,1u<<v,1u<<v);
 int id,k;while(cin>>id>>k){vector<int> p(k);for(int &x:p)cin>>x;if(!valid(p))abort();
  auto src=parts(p),v=src;auto [len,bad]=stats(v);if(bad||len!=p.size())abort();int best=0,bestNew=0,changed=0,low=9999,accepted=0;Segs win;set<vector<int>>seen;
  for(int it=0;it<steps;++it){
   int phase=it%1000;if(!phase){v=src;len=k;bad=0;}
   double temp=0.16+1.25*(1.-phase/1000.),fee=3.7+5.2*phase/1000.;
   auto w=v;if(!mutate(w,pick(13),fee))continue;auto [l,b]=stats(w);
   if(l>=193 && b<low){low=b;if(b<=2){cerr<<id<<" "<<b<<" "<<l;for(int x:flat(w))cerr<<" "<<x;cerr<<endl;}}
   if(!b && l>=k-3){auto z=flat(w);if(!valid(z)||z.size()!=l)abort();
    if(z!=p&&seen.insert(z).second){++changed;vector<int>a,c;for(auto &x:src)a.push_back(x.c);for(auto&x:w)c.push_back(x.c);if(a!=c)bestNew=max(bestNew,l-1);
      if(l-1>best){best=l-1;win=w;}}
    if(l-1>=goal && z!=p)break;
   }
   double delta=l-len-fee*(b-bad);if(delta>=0||generate_canonical<double,32>(rng)<exp(delta/temp)){v=move(w);len=l;bad=b;++accepted;}
  }
  cout<<id<<" "<<src.size()<<" "<<accepted<<" "<<changed<<" "<<best<<" "<<bestNew<<" "<<low;
  if(!win.empty())for(int x:flat(win))cout<<" "<<x;cout<<endl;
 }
}
