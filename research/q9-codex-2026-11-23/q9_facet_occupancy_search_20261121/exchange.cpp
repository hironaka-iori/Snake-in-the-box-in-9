#define Q9_OCCUPANCY_LIBRARY
#include "search.cpp"
#undef Q9_OCCUPANCY_LIBRARY
#include <unordered_set>
struct Complete{
 Job& job;State s;Mask start;vector<int> before,outs,unavailable;vector<int> rem,path;array<int,2> demand{};int k;
 long long removeStates=0,linear=0,leaves=0;unordered_set<unsigned long long> seen;
 Complete(Job&j):job(j),s(points(j.parts[2])),start(j.parts[2]){
  for(int v:points(job.parts[1])){if(!s.on[v])outs.push_back(v);else if(!has(job.parts[0],v))before.push_back(v);}
 }
 bool add(const vector<int>&possible,int from,int left){
  if(!left){++leaves;if(s.over()||s.hist[0]||s.hist[1]!=2)return false;auto t=s.inspect(true);
   if(t.groups>1)return false;path=t.longest;return true;
  }
  for(int i=from;i+left<=possible.size();++i){int x=possible[i],b=side(x);
   if(!demand[b]||s.load[x]>2)continue;bool ok=true;
   for(int d=0;d<9;++d){int v=x^(1<<d);if(s.on[v]&&s.load[v]>=2){ok=false;break;}}
   if(!ok)continue;
   s.edit(x,1);--demand[b];bool f=add(possible,i+1,left-1);++demand[b];s.edit(x,-1);if(f)return true;
  }
  return false;
 }
 bool attempt(){
  auto key=rem;sort(key.begin(),key.end());unsigned long long code=1;
  for(int x:key)code=code*512+x;
  if(!seen.insert(code).second)return false;++removeStates;
  if(s.over())return false;auto t=s.inspect();if(t.cycles||t.groups>k+1)return false;++linear;
  vector<int> possible;for(int x:outs){if(!demand[side(x)]||s.load[x]>2)continue;bool allowed=true;
   for(int d=0;d<9;++d){int y=x^(1<<d);if(s.on[y]&&s.load[y]>=2){allowed=false;break;}}
   if(allowed)possible.push_back(x);
  }
  return add(possible,0,k);
 }
 bool remove(int next){
  if(rem.size()==k)return attempt();
  int bad=-1;
  if(s.over())for(int v=0;v<512;++v)if(s.on[v]&&s.load[v]>2){bad=v;break;}
  auto choose=[&](int v,int idx){
   if(!s.on[v]||has(job.parts[0],v))return false;
   rem.push_back(v);++demand[side(v)];s.edit(v,-1);
   bool ok=remove(idx);s.edit(v,1);--demand[side(v)];rem.pop_back();return ok;
  };
  if(bad>=0){
   if(choose(bad,0))return true;
   for(int d=0;d<9;++d)if(choose(bad^(1<<d),0))return true;
  }else for(int j=next;j<before.size();++j)if(choose(before[j],j+1))return true;
  return false;
 }
 bool solve(int lim){for(k=1;k<=lim;++k)if(remove(0))return true;return false;}
};
int main(int argc,char**argv){
 int limit=stoi(argv[1]);Job j;while(cin>>j.id>>j.goal>>j.major){
  for(auto&m:j.parts)for(auto&v:m)cin>>v;for(int&v:j.lp)cin>>v;
  Complete c(j);bool ok=c.solve(limit);cout<<j.id<<" "<<(ok?"FOUND":"EXHAUSTED")<<" "<<c.removeStates<<" "<<c.linear<<" "<<c.leaves;
  if(ok){if(c.path.size()!=j.goal+1)abort();for(int i=0;i<c.path.size();++i)for(int h=0;h<i;++h)if(c.path[i]==c.path[h]||has_single_bit(unsigned(c.path[i]^c.path[h]))!=(h+1==i))abort();for(int v:c.path)cout<<" "<<v;}
  cout<<endl;if(ok&&j.goal==192)return 0;
 }
}
