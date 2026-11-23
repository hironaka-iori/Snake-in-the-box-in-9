#define Q7_FOUR_LIBRARY
#include "search_q7_four_q5.cpp"
#include <fstream>
#include <set>
struct Bank{
 Runner &r;int threshold;ofstream file;std::set<string> seen;uint64_t nodes=0,counts[60]{};
 array<U,4> masks{};array<int,4>end{};array<vector<int>,4> paths;
 void emit(int sz){
  const int g[4]={0,1,3,2};vector<int> p;
  for(int k=0;k<4;k++)for(int y:paths[k])p.push_back(32*g[k]+y);
  int names[7]={-1,-1,-1,-1,-1,5,6},next=0;string w;
  for(int i=1;i<p.size();i++){int d=countr_zero(unsigned(p[i-1]^p[i]));if(names[d]<0)names[d]=next++;w+=char('0'+names[d]);}
  if(seen.insert(w).second){counts[sz]++;file<<w<<'\n';}
 }
 void extend(int k,int sum,int x,U m,U blocked){
  nodes++;int n=popcount(m);
  if(sum+n+14*(3-k)>=threshold){
   int root=end[k-1];int shape=label.at({translate(m,root),x^root});
   if(sum+n+r.future[3-k][shape]>=threshold){
    masks[k]=m;end[k]=x;
    if(k==3)emit(sum+n);
    else{
     U ban=m&~(U(1)<<x);if(k==2)ban|=masks[0];
     if(!(ban&(U(1)<<x))){paths[k+1]={x};extend(k+1,sum+n,x,U(1)<<x,ban);}
    }
   }
  }
  for(U rem=nb[x]&~(blocked|m);rem;rem&=rem-1){int y=countr_zero(rem);paths[k].push_back(y);
   extend(k,sum,y,m|(U(1)<<y),blocked|nb[x]);paths[k].pop_back();}
 }
 void run(){
  for(int id:rep){auto a=rows[id];if(a.n+r.future[3][a.shape]<threshold)continue;
   int prev=-1,x=0;paths[0].clear();
   while(true){paths[0].push_back(x);U opts=a.mask&nb[x];if(prev>=0)opts&=~(U(1)<<prev);if(!opts)break;prev=x;x=countr_zero(opts);}
   masks[0]=a.mask;end[0]=a.end;paths[1]={a.end};extend(1,a.n,a.end,U(1)<<a.end,a.mask&~(U(1)<<a.end));
  }
  for(int j=threshold;j<=52;j++)cout<<"ROWS "<<j<<" "<<counts[j]<<endl;
  cout<<"DONE nodes "<<nodes<<endl;
 }
};
int main(int argc,char**argv){
 if(argc!=3)return 2;Runner r(0,1,1);r.init();Bank b{r,stoi(argv[1]),ofstream(argv[2])};if(!b.file)return 3;b.run();
}
