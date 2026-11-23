#define main bank_main
#include "join.cpp"
#undef main
uint8_t contacts[128]{},present[128]{};
string seq;
uint64_t dfsnodes=0,counts[60]{};
int threshold,upper,head;
void mark(int x,int del){present[x]=del>0;for(int i=0;i<7;i++)contacts[x^(1<<i)]+=del;}
void enumerate(int x,int layer,int n,int prev,int named){
 dfsnodes++;const int chain[]={0,14,26,39};
 if(prev+14+chain[3-layer]<threshold)return;
 if(layer==3&&prev+n>=threshold&&prev+n<=upper){counts[prev+n]++;if(join(seq)){cout<<"FOUND "<<seq<<endl;exit(0);}}
 for(int sym=0;sym<=5;sym++){
  bool cross=sym==5;if(cross&&(layer==3||prev+n+chain[3-layer]<threshold))continue;
  if(!cross&&(sym>named||(!layer&&n>=head)))continue;
  if(cross&&!layer&&n!=head)continue;
  int d=cross?(layer==1?6:5):sym,y=x^(1<<d);
  if(present[y]||contacts[y]!=1)continue;
  mark(y,1);seq.push_back('0'+d);enumerate(y,layer+cross,cross?1:n+1,cross?prev+n:prev,named+(!cross&&sym==named));seq.pop_back();mark(y,-1);
 }
}
int main(int argc,char**argv){
 if(argc!=6)return 2;goal=stoi(argv[1]);threshold=stoi(argv[2]);upper=stoi(argv[3]);
 for(int v=0;v<32;v++)for(int d=0;d<5;d++)N[v]|=U(1)<<(v^(1<<d));
 mark(0,1);for(head=stoi(argv[4]);head<=stoi(argv[5]);head++){
 enumerate(0,0,1,0,0);cout<<"CUM_HEAD "<<head<<" dfs "<<dfsnodes<<" cores";for(int j=threshold;j<=upper;j++)cout<<" "<<j<<"="<<counts[j];cout<<" joins";for(auto v:tests)cout<<" "<<v;cout<<endl;}
 cout<<"DONE"<<endl;
}
