// Connect every retained component in a given order, then extend both endpoints.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>
using namespace std;using Path=vector<int>;
struct Connect{
 vector<Path> parts,links;int target,extra,cap,nodes=0;bool capped=false;
 array<bool,512> used{};array<int,512> nb{};Path final;
 int dist(int a,int b){return __builtin_popcount(unsigned(a^b));}
 void toggle(int x,int d){used[x]=d>0;for(int b=0;b<9;b++)nb[x^(1<<b)]+=d;}
 bool grow(Path&p,bool second){
 if((int)p.size()>=target+1){final=p;return true;}
 if(++nodes>cap){capped=true;return false;}
 for(int d=0;d<9;d++){int x=p.back()^(1<<d);if(used[x]||nb[x]!=1)continue;
 toggle(x,1);p.push_back(x);if(grow(p,second))return true;p.pop_back();toggle(x,-1);if(capped)return false;}
 if(!second){reverse(p.begin(),p.end());bool ok=grow(p,true);reverse(p.begin(),p.end());if(ok)return true;}
 return false;
 }
 bool bridge(int j,int tip,int left){
 if(++nodes>cap){capped=true;return false;}
 if(j==(int)parts.size()-1){Path p;for(size_t i=0;i<parts.size();i++){p.insert(p.end(),parts[i].begin(),parts[i].end());if(i<links.size())p.insert(p.end(),links[i].begin(),links[i].end());}return grow(p,false);}
 int end=parts[j+1].front(),reserve=0;for(int i=j+1;i<(int)parts.size()-1;i++)reserve+=max(0,dist(parts[i].back(),parts[i+1].front())-1);
 if(left-reserve<dist(tip,end)-1)return false;
 for(int d=0;d<9;d++){
 int x=tip^(1<<d);if(used[x]||left<=reserve)continue;
 bool last=dist(x,end)==1;if(nb[x]!=(last?2:1))continue;
 toggle(x,1);links[j].push_back(x);
 if(last?bridge(j+1,parts[j+1].back(),left-1):bridge(j,x,left-1))return true;
 links[j].pop_back();toggle(x,-1);if(capped)return false;
 }return false;
 }
 bool solve(){links.resize(parts.size()-1);for(auto&p:parts)for(int v:p)toggle(v,1);return bridge(0,parts[0].back(),extra);}
};
bool valid(const Path&p){for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){int d=__builtin_popcount(unsigned(p[i]^p[j]));if(d==0||((d==1)!=(j+1==i)))return false;}return true;}
int main(int argc,char**argv){if(argc!=5)return 2;int target=atoi(argv[1]),reps=atoi(argv[2]),cap=atoi(argv[3]),seed=atoi(argv[4]);mt19937 gen(seed);
 long long templates=0,nodes=0,caps=0;int rows=0;string l;
 while(getline(cin,l)){istringstream s(l);int dim,st,n,v;s>>dim>>st>>n;vector<Path> comps(1);
 while(s>>v){if(!comps.back().empty()&&__builtin_popcount(unsigned(comps.back().back()^v))!=1)comps.emplace_back();comps.back().push_back(v);}
 if((int)comps.size()!=st)return 3;if(st<2||st>6)continue;rows++;
 for(int z=0;z<reps;z++){
 auto p=comps;
 if(z<8&&st==2){if(z&4)swap(p[0],p[1]);for(int i=0;i<2;i++)if(z&(1<<i))reverse(p[i].begin(),p[i].end());}
 else{shuffle(p.begin(),p.end(),gen);for(auto &q:p){if(gen()%2)reverse(q.begin(),q.end());
 if(z%4){int a=min(int(gen()%5),int(q.size())-1);q.erase(q.begin(),q.begin()+a);
 int b=min(int(gen()%5),int(q.size())-1);q.resize(q.size()-b);}}}
 int kept=0,lb=0;for(auto&q:p)kept+=q.size();for(int i=1;i<st;i++)lb+=__builtin_popcount(unsigned(p[i-1].back()^p[i].front()))-1;
 int limit=max(target+1-kept+4,lb+4);if(limit>45)continue;
 Connect c{p,{},target,limit,cap};templates++;
 if(c.solve()){if(!valid(c.final)||(int)c.final.size()<=target)abort();cout<<"FOUND";for(int x:c.final)cout<<" "<<x;cout<<endl;return 0;}
 caps+=c.capped;nodes+=c.nodes;
 }}
 cout<<"DONE sections "<<rows<<" templates "<<templates<<" capped "<<caps<<" nodes "<<nodes<<endl;
}
