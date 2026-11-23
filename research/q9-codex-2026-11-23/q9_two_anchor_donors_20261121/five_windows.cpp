#define main sampled_main
#include "search.cpp"
#undef main
int main(){
 vector<Path> bank;string line;while(cin>>line){Path p{0};for(char c:line)p.push_back(p.back()^(1<<(c-'0')));assert(p.size()==192&&valid(p));bank.push_back(p);}
 assert(bank.size()==131);const auto &p=bank[0];
 for(auto [a,b]:vector<pair<int,int>>{{5,30},{6,75},{20,140},{37,159},{65,170}}){
  Host h(p,a,b);int l=b-a+1,shifts=0;uint64_t cases=0,nodes=0;
  for(int sh=0;sh<512;sh++){
   int goal=p[a]^p[b]^sh;int d=popcount(unsigned(goal));
   if(((d^l)&1)||d<2||!h.feasible(sh))continue;
   shifts++;auto bad=h.blocked(sh);
   for(int src=1;src<(int)bank.size();src++)for(bool backward:{false,true}){
    Path q=bank[src];if(backward)reverse(q.begin(),q.end());
    for(int j=0;j+l<(int)q.size();j++)if(popcount(unsigned(q[j]^q[j+l]))==d){
     cases++;Test t(h,q,j,l,sh,bad,nodes);if(t.search(0,511)){
      auto w=t.recover();cout<<"FOUND interval "<<a<<" "<<b<<" donor "<<src<<" vertices";for(int x:w)cout<<" "<<x;cout<<endl;return 0;}
    }
   }
  }
  cout<<"WINDOW "<<a<<" "<<b<<" graft_length "<<l<<" viable_shifts "<<shifts<<" matched_placements "<<cases<<" assignment_nodes "<<nodes<<endl;
 }
 cout<<"DONE"<<endl;
}
