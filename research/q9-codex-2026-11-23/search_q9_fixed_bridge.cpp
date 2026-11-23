// Preserve the length, replace an interval of vertices near a chord by a new walk.
#define main fixed_walk_original_main
#include "search_q9_fixed_walk.cpp"
#undef main
#include <fstream>
#include <unordered_set>
#include <numeric>

string key(const vector<int>& p){
 string f,b;
 for(int rev=0;rev<2;rev++){
  array<int,9> label;label.fill(-1);int next=0;
  string s;
  for(int t=1;t<(int)p.size();t++){
   int i=rev?(int)p.size()-t:t;
   int d=countr_zero((unsigned)(p[i]^p[i-1]));
   if(label[d]<0)label[d]=next++;
   s.push_back(char(label[d]));
  }
  if(rev)b=s;else f=s;
 }
 return min(f,b);
}
struct Bridge {
 Search &s; Walk &w;
 int first,last,right,limit,nodecap,spent=0;
 vector<int> chosen;
 bool dfs(int i,int prev,int cost,bool changed){
  if(++spent>nodecap)return false;
  if(i>last)return changed&&cost<=limit;
  struct Opt{int priority,v,cost;};array<Opt,9> opt;int n=0;
  for(int d=0;d<w.dim;d++){
   int v=prev^(1<<d);
   if(w.cnt[v])continue;
   if(right>=0){
    int dist=popcount((unsigned)(v^right));
    if(dist>last-i+1||((dist^(last-i+1))&1))continue;
    if(i==last&&dist!=1)continue;
   }
   int delta=w.near[v]-1-(i==last&&right>=0);
   if(delta<0)abort();
   if(cost+delta>limit)continue;
   // Randomize ties, mildly disfavor reconstructing the old interval.
   opt[n++]={s.pick(30)+8*delta+3*(v==w.p[i]),v,cost+delta};
  }
  sort(opt.begin(),opt.begin()+n,[](auto a,auto b){return a.priority<b.priority;});
  for(int k=0;k<n&&spent<nodecap;k++){
   int v=opt[k].v;chosen[i-first]=v;w.edit(v,1);
   if(dfs(i+1,v,opt[k].cost,changed||v!=w.p[i]))return true;
   w.edit(v,-1);
  }
  return false;
 }
 bool run(int allowed,int cap){
  int L=w.p.size()-1;
  array<int,512> where;where.fill(-1);
  for(int i=0;i<=L;i++)where[w.p[i]]=i;
  int selected=-1,edges=0;
  for(int i=0;i<=L;i++)for(int d=0;d<w.dim;d++){
   int j=where[w.p[i]^(1<<d)];
   if(j>i+1 && s.pick(++edges)==0)selected=s.pick(2)?j:i;
  }
  if(selected<0)return false;
  int size=5+s.pick(s.pick(2)?16:46);
  size=min(size,L-1);
  if(s.pick(7)==0)selected=s.pick(L+1);
  if(selected==0||s.pick(2)){reverse(w.p.begin(),w.p.end());selected=L-selected;}
  first=max(1,selected-s.pick(size));last=min(L,first+size-1);
  if(selected>=L-size&&s.pick(2)){last=L;first=L-size+1;}
  if(selected<first&&selected>0){first=selected;last=min(L,first+size-1);}
  right=last==L?-1:w.p[last+1];
  limit=allowed;nodecap=cap;chosen.resize(last-first+1);
  int old=w.E;
  for(int i=first;i<=last;i++)w.edit(w.p[i],-1);
  int fixed_cost=w.E+(last-first+1)+(right>=0);
  if(fixed_cost<0)abort();
  if(fixed_cost<=limit&&dfs(first,w.p[first-1],fixed_cost,false)){
   copy(chosen.begin(),chosen.end(),w.p.begin()+first);
   if(w.E>limit)abort();return true;
  }
  for(int i=first;i<=last;i++)w.edit(w.p[i],1);
  if(w.E!=old)abort();return false;
 }
};
#ifndef Q9_FIXED_BRIDGE_NO_DRIVER
int main(int argc,char**argv){
 if(argc!=7&&argc!=8)return 2;
 bool mixed=argc==8;
 int L=stoi(argv[1]),epochs=stoi(argv[2]),iter=stoi(argv[3]),cap=stoi(argv[4]);
 Search s{mt19937_64(stoull(argv[5]))};ofstream save(argv[6]);if(!save)return 3;
 string line;vector<vector<int>> seeds,pool;
 while(getline(cin,line)){
  istringstream in(line);vector<int> p;int v;
  while(in>>v){if(v<0||v>511)return 4;p.push_back(v);}
  if(p.empty())continue;
  Walk w(9,p);w.verify();if(w.E>3||p.size()<size_t(L-5))return 5;seeds.push_back(p);
 }
 if(seeds.empty())return 6;
 unordered_set<string> seen;
 long long proposals=0,accepted=0,expanded=0;int best=999;
 auto observe=[&](Walk&w){
  best=min(best,w.E);
  if(w.E<=1){
   w.verify();
   if(w.E==0){cout<<"FOUND";for(int v:w.p)cout<<" "<<v;cout<<endl;return true;}
   if(seen.insert(key(w.p)).second){
    for(size_t i=0;i<w.p.size();i++)save<<(i?" ":"")<<w.p[i];save<<endl;
    if(pool.size()<5000)pool.push_back(w.p);else if(s.pick(3)==0)pool[s.pick(pool.size())]=w.p;
   }
  }
  return false;
 };
 for(int epoch=0;epoch<epochs;epoch++){
  vector<int> p=(!pool.empty()&&s.pick(100)<62)?pool[s.pick(pool.size())]:seeds[s.pick(seeds.size())];
  if(s.pick(2))reverse(p.begin(),p.end());
  if((int)p.size()>=L+1&&Walk(9,p).E==0)p.resize(L);
  if((int)p.size()>L+1)p.resize(L+1);
  Walk w(9,p);
  while((int)w.p.size()<L+1){
   int bestcost=999,y=-1;
   for(int d=0;d<9;d++){int q=w.p.back()^(1<<d);if(w.cnt[q])continue;
    int score=100*abs(w.near[q]-2)+s.pick(50);if(score<bestcost){bestcost=score;y=q;}}
   if(y<0)break;w.p.push_back(y);w.edit(y,1);--w.E;
  }
  if((int)w.p.size()!=L+1)continue;
  if(observe(w))return 0;
  for(int it=0;it<iter;it++){
   if(it%100==0)w.verify();
   int old=w.E;
   Walk prev=w;
   int t=s.pick(100);int lim=max(0,old+(t<50?-1:t<77?0:1));
   Bridge b{s,w};bool ok;
   if(mixed&&s.pick(100)<18){
    ok=s.move(w,.8);
    if(w.E>5){w=prev;ok=false;}
   }else ok=b.run(min(5,lim),cap);
   expanded+=b.spent;proposals++;
   if(ok){
    double frac=1.-double(it%160)/160.;
    if(s.accept(w.E-old,(mixed?.24:.14)+(mixed?1.40:.70)*frac*frac)){accepted++;if(observe(w))return 0;}
    else w=move(prev);
   }
  }
  if((epoch+1)%10==0||epoch+1==epochs)
   cout<<"CHECK "<<epoch+1<<" proposals "<<proposals<<" accepted "<<accepted<<" DFS "<<expanded<<" distinct_one "<<seen.size()<<" best "<<best<<endl;
 }
}

#endif
