// Enumerate all choices of vertical edges on small walks and compare the exact optimum.
#define main projection_driver
#include "search_q9_projection_lifts.cpp"
#undef main
long long walks=0, masks=0;
void checkWalk(Path &p){
 int n=p.size(),best=-1;
 for(int s=0;s<(1<<n);++s){++masks;int bit=0;Path q;
  for(int i=0;i<n;++i){q.push_back(p[i]+bit);if((s>>i)&1){bit^=256;q.push_back(p[i]+bit);}}
  if(valid(q,9))best=std::max(best,(int)q.size()-1);
 }
 Lift l(p);int result=-1;
 if(l.prepare())for(int k=l.base;k>=n-1;--k)if(l.search(0,l.base-k)){
  auto q=l.build();if(!valid(q,9)||(int)q.size()!=k+1)std::abort();result=k;break;
 }
 if(result!=best)std::abort();++walks;
}
void enumerate(Path &p,int used){checkWalk(p);for(int d=0;d<3;++d){int v=p.back()^(1<<d);if((used>>v)&1)continue;p.push_back(v);enumerate(p,used|(1<<v));p.pop_back();}}
int main(){Path p{0};enumerate(p,1);std::mt19937 gen(9231);
 for(int r=0;r<2000;++r){p={0};for(int i=1;i<11;++i){Path opts;for(int d=0;d<4;++d){int v=p.back()^(1<<d);if(std::find(p.begin(),p.end(),v)==p.end())opts.push_back(v);}if(opts.empty())break;p.push_back(opts[gen()%opts.size()]);}checkWalk(p);}
 std::cout<<"MATCH walks "<<walks<<" switch_masks "<<masks<<std::endl;}
