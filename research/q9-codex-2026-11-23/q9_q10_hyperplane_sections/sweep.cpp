// Exact basis search in original slice coordinates. A single traversal answers several allowed lengths.
#define main old_main
#include "../q9_change_basis/find.cpp"
#undef main
#include "../q9_change_basis/forest_focus.hpp"
#include <bit>
using namespace std;
struct Sweep{
 vector<int> p,bs,goals,answer;array<int,512> weight{};array<Bits,512> support{};Bits membership;uint64_t nodes=0,ranked=0;array<int,3> tried{};bool found=false;int maxh=0,success=0;
 Sweep(vector<int> row,vector<int> ts):p(row),goals(ts){
  for(int t:ts)maxh=max(maxh,t+1-(int)p.size());for(int x:p)membership.set(x);
  for(int g=1;g<512;g++){for(int x:p)if(membership[x^g])support[g].set(x);weight[g]=support[g].count()/2;}
 }
 virtual bool finish(int edges){
  array<int,512> coord;coord.fill(-1);coord[0]=0;vector<int> span{0};
  for(int a=0;a<9;a++){int g=bs[a];if(coord[g]>=0)return false;int n=span.size();
   for(int k=0;k<n;k++){int y=span[k]^g;coord[y]=coord[span[k]]^(1<<a);span.push_back(y);}
  }ranked++;Bits selected;for(int x:p)selected.set(coord[x]);
  for(int j=0;j<goals.size();j++){int t=goals[j],h=t+1-p.size();if(h<0||edges<(int)p.size()-1-h)continue;tried[j]++;
   unordered_set<Bits> dead;vector<int> path;if(grow_focus(selected,h,path,dead)){success=t;answer=path;return true;}}
  return false;
 }
 bool dfs(const vector<int>& options,const Bits& once,const Bits& twice,int edges){
  nodes++;int need=9-bs.size(),num=options.size();if(num<need)return false;
  int hi=edges;for(int i=num-need;i<num;i++)hi+=weight[options[i]];if(hi<(int)p.size()-1-maxh)return false;
  for(int i=0;i+need<=num;i++){
   int lo=edges;for(int k=i;k<i+need;k++)lo+=weight[options[k]];if(lo>(int)p.size()-1)break;
   int g=options[i],sum=edges+weight[g];bs.push_back(g);
   if(need==1){if(sum>=(int)p.size()-1-maxh && finish(sum))return true;}
   else{Bits next2=twice|(once&support[g]);vector<int> avail;int cap=(int)p.size()-1-sum-(need-2)*weight[g];
    for(int k=i+1;k<num;k++){int x=options[k];if(weight[x]>cap)break;if((support[x]&next2).none())avail.push_back(x);}
    if(dfs(avail,once^support[g],next2,sum))return true;
   }bs.pop_back();
  }return false;
 }
 void run(int r,int mask,int side){
  vector<int> options(511);iota(options.begin(),options.end(),1);sort(options.begin(),options.end(),[&](int a,int b){return pair(weight[a],a)<pair(weight[b],b);});
  found=dfs(options,Bits{},Bits{},0);
  cout<<r<<" "<<mask<<" "<<side<<" "<<p.size()<<" "<<(found?"FOUND":"CLOSED")<<" "<<nodes<<" "<<ranked;
  for(int j=0;j<goals.size();j++)cout<<" "<<goals[j]<<"="<<tried[j];if(found){cout<<" TARGET "<<success<<" BASIS";for(int g:bs)cout<<" "<<g;cout<<" PATH";for(int x:answer)cout<<" "<<x;}cout<<endl;
 }
};
#ifndef SWEEP_ONLY
int main(int argc,char**argv){if(argc!=4&&argc!=5)return 2;int low=atoi(argv[1]),high=atoi(argv[2]),just=atoi(argv[3]);string line;
 while(getline(cin,line)){istringstream f(line);int r,m,b,n,x;f>>r>>m>>b>>n;vector<int> p;while(f>>x)p.push_back(x);if(n!=p.size()||n<low||n>high||(just&&m!=just))continue;
 vector<int> targets;vector<int> requested=argc==5?vector<int>{atoi(argv[4])}:vector<int>{192,195,196};for(int t:requested)if(n<=t+1)targets.push_back(t);if(targets.empty())continue;
 Sweep s(p,targets);s.run(r,m,b);if(s.found)return 0;
 }}

#endif
