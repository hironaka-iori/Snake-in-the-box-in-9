#define main donor_main
#include "../q9_change_basis/find.cpp"
#undef main
#ifdef DIRECT_FILL
#include "direct_fill.hpp"
#else
#include "../q9_change_basis/forest.hpp"
#endif
struct Gl{
 Search base;vector<int> chosen;long long nodes=0,closures=0,cap;bool unknown=false;int minweight,maxweight,tag;
 Gl(vector<int> a,int goal,long long limit,int index):base(a,goal),cap(limit),tag(index){int n=a.size();maxweight=n-1;minweight=maxweight-(goal+1-n);}
 bool run(const vector<int>&opts,int left,int weight,const Bits&once,const Bits&twice,const vector<int>&space){
  if(nodes++>=cap){unknown=true;return false;}int n=opts.size();if(n<left)return false;int low=weight,high=weight;for(int j=0;j<left;j++){low+=base.edges[opts[j]];high+=base.edges[opts[n-1-j]];}if(low>maxweight||high<minweight)return false;
  for(int j=0;j+left<=n;j++){int g=opts[j],sum=weight+base.edges[g];if(weight+left*base.edges[g]>maxweight)break;
   chosen.push_back(g);
   if(left==1){if(sum>=minweight&&sum<=maxweight){closures++;if(complete_forest(chosen,base.points,base.target,tag))return true;}}
   else{
    Bits once2=once^base.hits[g],twice2=twice|(once&base.hits[g]);vector<int> ext=space;Bits sp;
    for(int k:space){ext.push_back(k^g);sp.set(k);sp.set(k^g); }
    vector<int> next;int ceiling=maxweight-sum-(left-2)*base.edges[g];
    for(int h=j+1;h<n;h++){int v=opts[h];if(base.edges[v]>ceiling)break;if(!sp[v]&&!(twice2&base.hits[v]).any())next.push_back(v);}
    if(run(next,left-1,sum,once2,twice2,ext))return true;
   }chosen.pop_back();if(unknown)break;
  }return false;
 }
};
int main(int argc,char**argv){if(argc!=3)return 2;int goal=atoi(argv[1]);long long cap=atoll(argv[2]);string l;int index=0;while(getline(cin,l)){istringstream is(l);string t;is>>t;if(t!="points")return 2;int x;vector<int>p;Bits b;while(is>>x){if(x<0||x>511||b[x])return 3;p.push_back(x);b.set(x);}Gl s(p,goal,cap,index);vector<int>opts(511);iota(opts.begin(),opts.end(),1);sort(opts.begin(),opts.end(),[&](int x,int y){return s.base.edges[x]!=s.base.edges[y]?s.base.edges[x]<s.base.edges[y]:x<y;});vector<int> span{0};bool hit=s.run(opts,9,0,Bits(),Bits(),span);cout<<"R "<<index++<<" "<<(hit?"FOUND":s.unknown?"UNKNOWN":"CLOSED")<<" "<<s.nodes<<" "<<s.closures<<endl;if(hit)break;}}
