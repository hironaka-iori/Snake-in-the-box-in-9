#define main anneal_main
#include "coupled.cpp"
#undef main
#include <sstream>
struct Seed{State s;string w;int score;};
State trial,pick;int lo,hi,floorScore,budget,used,bestV,draws,retained,parentlen;uint64_t nodes=0,calls=0,solutions=0;int relaxed[]={0,14,26,39,52,64,77,90,102,115,128,141,154};
void layer(int k,int sum);
void walk(int k,int sum,int x,U m,U deny,int dest){
 if(used++>=budget)return;nodes++;
 int n=popcount(m);if(sum+n+relaxed[hi-k]>=floorScore){
  if(k<hi){trial.m[k]=m;trial.p[k+1]=x;layer(k+1,sum+n);}
  else if(dest<0||dest==x){solutions++;float val=sum+n;if(val>bestV){bestV=val;draws=0;}
   if(val==bestV&&(rnd()%++draws)==0){trial.m[k]=m;trial.p[k+1]=x;pick=trial;retained=1;}}
 }
 if(used>=budget||(k==hi&&x==dest))return;
 U next=nbs[x]&~(m|deny);
 while(next&&used<budget){int idx=rnd()%popcount(next);U z=next;for(int i=0;i<idx;i++)z&=z-1;
  int y=countr_zero(z);next^=1u<<y;walk(k,sum,y,m|(1u<<y),deny|nbs[x],dest);}
}
void layer(int k,int sum){
 if(used>=budget||sum+relaxed[hi-k+1]<floorScore)return;
 int root=trial.p[k],dest=k==hi&&hi<15?trial.p[hi+1]:-1;U ban=0;
 for(int d=0;d<4;d++){int j=adj[k][d];if(j>=k&&j<=hi)continue;U mask=trial.m[j];
  if(j==k-1)mask&=~(1u<<root);if(j==k+1&&dest>=0)mask&=~(1u<<dest);
  ban|=mask;
 }if((ban>>root)&1u)return;if(dest>=0&&((ban>>dest)&1u))return;
 walk(k,sum,root,1u<<root,ban,dest);
}
void order(const string&w,bool rev){gray[0]=0;for(int k=0;k<15;k++)gray[k+1]=gray[k]^(1<<(w[k]-'0'));if(rev)reverse(gray,gray+16);int ix[16];for(int k=0;k<16;k++)ix[gray[k]]=k;
 for(int k=0;k<16;k++)for(int d=0;d<4;d++)adj[k][d]=ix[gray[k]^(1<<d)];}
void flip(State&s){reverse(s.m.begin(),s.m.end());reverse(s.p.begin(),s.p.end());}
int main(int argc,char**argv){
 if(argc!=5)return 2;seed=stoul(argv[2]);int runs=stoi(argv[3]),steps=stoi(argv[4]);ifstream file(argv[1]);string line;vector<Seed> starts;
 for(int x=0;x<32;x++)for(int d=0;d<5;d++)nbs[x]|=1u<<(x^(1<<d));
 while(getline(file,line)){istringstream l(line);string a,w;int n,r,it,x,k=-1,last=-1;l>>a;if(a!="BEST")continue;l>>n>>w>>r>>it;State s;while(l>>x){if(x/32!=last){if(++k>15)abort();s.p[k]=x%32;last=x/32;}s.m[k]|=1u<<(x%32);s.p[k+1]=x%32;}
  if(k!=15)continue;order(w,false);auto e=eval(s);if(e.n!=n+1||e.c)abort();starts.push_back({s,w,n});}
 if(starts.empty())return 3;stable_sort(starts.begin(),starts.end(),[](auto&a,auto&b){return a.score>b.score;});int global=starts[0].score;
 for(int run=0;run<runs;run++){int idx=rnd()%min(int(starts.size()),run%3?32:160);auto src=starts[idx];State state=src.s,elite=state;int high=src.score,stagnant=0;
  for(int t=0;t<steps;t++){bool rev=rnd()&1;order(src.w,rev);trial=state;if(rev)flip(trial);
   int u=rnd()%100;int size=u<32?1:u<65?2:u<85?3:4+rnd()%4;lo=1+rnd()%(16-size);hi=lo+size-1;if(rnd()%5==0)hi=15,lo=16-size;
   parentlen=0;for(int j=lo;j<=hi;j++)parentlen+=popcount(trial.m[j]);floorScore=parentlen-(rnd()%10==0?2:0);
   bestV=-1;used=0;retained=0;budget=size<=2?7000:5000+rnd()%9000;layer(lo,0);calls++;
   if(retained){if(rev)flip(pick);state=pick;order(src.w,false);auto e=eval(state);if(e.c)abort();
    if(e.n-1>high){high=e.n-1;elite=state;stagnant=0;if(high>global){global=high;writeBest(state,src.w,run,t);if(global>=192)return 0;}}
   }
   if(++stagnant==70){state=elite;stagnant=0;}
  }if(high>starts[idx].score)starts[idx]={elite,src.w,high};
  cout<<"RUN "<<run<<" source "<<src.score<<" best "<<high<<" global "<<global<<" calls "<<calls<<" nodes "<<nodes<<" feasible "<<solutions<<endl;
 }
}
