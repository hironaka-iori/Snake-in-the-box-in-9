// Construct odd-length snakes by freely choosing a Hamiltonian order of
// a fixed parity class and all clean intervening vertices.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <fstream>
#include <sstream>
#include <set>
using Path=vector<int>;
string key191(const Path&p){
 auto side=[&](bool rev){array<int,9> axis;axis.fill(-1);int next=0;string s;
  for(int j=1;j<(int)p.size();j++){int i=rev?int(p.size())-j:j,v=countr_zero((unsigned)(p[i]^p[i-1]));
   if(axis[v]<0)axis[v]=next++;s+=char('a'+axis[v]);}return s;};
 return min(side(false),side(true));
}
bool verify191(const Path&p){
 for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){int d=popcount(unsigned(p[i]^p[j]));
  if(!d||(d==1)!=(j+1==i))return false;}
 return true;
}
struct Odd {
 set<string> known,novel;uint64_t tested=0,orders=0,unknown=0,lifts=0,recoveries=0;int limit;
 Odd(const string&file,int cap):limit(cap){ifstream f(file);string l;while(getline(f,l)){istringstream r(l);Path p;int x;
  while(r>>x)p.push_back(x);if(p.size()!=192||!verify191(p))abort();known.insert(key191(p));}if(known.empty())abort();}
 bool inspect(Path p){
  lifts++;string s=key191(p);if(known.contains(s)){recoveries++;return false;}
  if(!novel.insert(s).second)return false;
  if(!verify191(p))abort();cout<<"NOVEL191";for(int x:p)cout<<' '<<x;cout<<endl;
  for(int rev=0;rev<2;rev++){for(int j=0;j<9;j++){auto q=p;q.push_back(p.back()^(1<<j));if(verify191(q)){
   cout<<"FOUND192";for(int x:q)cout<<' '<<x;cout<<endl;return true;}}reverse(p.begin(),p.end());}return false;
 }
 bool test(const Path&a){
  ++tested;if(a.size()!=96)abort();Search s(a,10000,true);array<vector<int>,96> tail;
  Graph g(a,limit);for(int v=0;v<512;v++){unsigned m=s.axes[v];int deg=popcount(m);
   if(deg==1)tail[s.slot[v^(1<<countr_zero(m))]].push_back(v);
   else if(deg==2){int i=s.slot[v^(1<<countr_zero(m))];m&=m-1;g.add(i,s.slot[v^(1<<countr_zero(m))],v);}
  }
  vector<int> tips,forced;for(int i=0;i<96;i++){if(!tail[i].empty())tips.push_back(i);if(g.adj[i].empty())return false;if(g.adj[i].size()==1)forced.push_back(i);}
  if(tips.empty()||forced.size()>2)return false;
  for(int tip:tips){for(int end=0;end<96;end++){
   if(end==tip||(!tail[end].empty()&&end<tip))continue;
   if(any_of(forced.begin(),forced.end(),[&](int x){return x!=tip&&x!=end;}))continue;
   int n=g.edges.size();g.add(tip,g.dummy,-1);g.add(end,g.dummy,-1);g.witness.clear();g.nodes=0;
   int ret=g.visit(vector<int8_t>(g.edges.size()));g.adj[tip].pop_back();g.adj[end].pop_back();g.adj[g.dummy].clear();g.edges.resize(n);
   if(ret<0){unknown++;continue;}if(!ret)continue;orders++;
   auto base=g.witness;if(base.size()!=191)abort();if(base.front()==a[tip])reverse(base.begin(),base.end());if(base.back()!=a[tip])abort();
   vector<pair<int,int>> alt;for(int i=1;i<190;i+=2){int other=base[i-1]^base[i]^base[i+1];if(popcount(unsigned(s.axes[other]))==2)alt.emplace_back(i,other);}
   int cases=1<<min(int(alt.size()),12);
   for(int mask=0;mask<cases;mask++){auto p=base;
    for(int j=0;j<min((int)alt.size(),12);j++)if(mask>>j&1)p[alt[j].first]=alt[j].second;
    for(int x:tail[tip]){p.push_back(x);if(inspect(p))return true;p.pop_back();}
    for(int x:tail[end]){p.insert(p.begin(),x);if(inspect(p))return true;p.erase(p.begin());}
   }
  }}
  return false;
 }
};
int main(int argc,char**argv){
 if(argc!=3)return 2;Odd s(argv[1],stoi(argv[2]));string l;while(getline(cin,l)){
  istringstream r(l);int x;Path a;while(r>>x)a.push_back(x);if(a.size()!=96)return 3;if(s.test(a))return 0;
  if(s.tested%1000==0)cout<<"RUN "<<s.tested<<" orders "<<s.orders<<" lifts "<<s.lifts<<" unknown "<<s.unknown<<" new "<<s.novel.size()<<endl;
 }cout<<"DONE "<<s.tested<<" orders "<<s.orders<<" lifts "<<s.lifts<<" known "<<s.recoveries<<" unknown "<<s.unknown<<" new "<<s.novel.size()<<endl;
}
