#define Q9_GRAY_LIBRARY
#include "search_q9_q5_gray.cpp"
#undef main
struct Four{
 Runner &r;int target;uint64_t nodes=0;
 array<U,4> mask{};array<int,4>end{};array<vector<int>,4> path;
 bool layer(int k,int score){
  int start=end[k-1];
  U blocked=mask[k-1]&~(U(1)<<start);if(k==3)blocked|=mask[0];
  if(blocked&(U(1)<<start))return false;
  return extend(k,score,start,U(1)<<start,blocked,vector<int>{start});
 }
 bool extend(int k,int score,int x,U m,U ban,vector<int> track){
  ++nodes;
  int n=popcount(m);
  if(n>=target-score-14*(3-k)){
    int root=end[k-1],shape=label.at({translate(m,root),x^root});
    if(score+n+r.future[3-k][shape]>=target){
      mask[k]=m;end[k]=x;path[k]=track;
      if(k==3||layer(k+1,score+n))return true;
    }
  }
  for(U options=nb[x]&~(ban|m);options;options&=options-1){
   int y=countr_zero(options);track.push_back(y);bool ok=extend(k,score,y,m|(U(1)<<y),ban|nb[x],track);track.pop_back();
   if(ok)return true;
  }return false;
 }
 bool run(){
  for(int id:rep){auto a=rows[id];if(a.n+r.future[3][a.shape]<target)continue;
   mask[0]=a.mask;end[0]=a.end;int prev=-1,x=0;path[0].clear();
   while(true){path[0].push_back(x);U opt=nb[x]&a.mask;if(prev>=0)opt&=~(U(1)<<prev);if(!opt)break;prev=x;x=countr_zero(opt);}
   if(layer(1,a.n)){
     vector<int> p;int gray[4]={0,1,3,2};for(int i=0;i<4;i++)for(int y:path[i])p.push_back(y+32*gray[i]);
     for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||has_single_bit(unsigned(p[i]^p[j]))!=(i==j+1))abort();
     cout<<"YES "<<target<<" "<<p.size()<<" vertices";for(int y:p)cout<<" "<<y;cout<<endl;return true;
   }
  }
  cout<<"NO "<<target<<" nodes "<<nodes<<endl;return false;
 }
};
#ifndef Q7_FOUR_LIBRARY
int main(){
 Runner runner(0,1,1);runner.init();
 for(int g=52;g>=42;--g){Four f{runner,g};if(f.run())return 0;}
}
#endif
