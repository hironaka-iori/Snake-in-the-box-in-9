#define main anneal_main
#include "coupled.cpp"
#undef main
#include <sstream>
struct Entry{State s;string order;int c,n;};
int sx(int x,int u,int v){return ((x>>u^x>>v)&1)?x^(1<<u)^(1<<v):x;}
U axes(U m,int u,int v){if(u==v)return m;U r=0;for(;m;m&=m-1)r|=1u<<sx(countr_zero(m),u,v);return r;}
void bestMask(State&s,int k,float lam,int noise){
 int root=s.p[k],diff=root^s.p[k+1];int top=-999999;U chosen=0;int lc=int(lam*16);U m0=s.m[adj[k][0]],m1=s.m[adj[k][1]],m2=s.m[adj[k][2]],m3=s.m[adj[k][3]];
 for(int i:cat[diff]){U m=shifted[root][i];int c=popcount(m&m0)+popcount(m&m1)+popcount(m&m2)+popcount(m&m3);
  int val=rows[i].n*16-lc*c+int(rnd()%noise);if(val>top){chosen=m;top=val;}}
 if(!chosen)abort();s.m[k]=chosen;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;seed=stoul(argv[2]);int runs=stoi(argv[3]),steps=stoi(argv[4]);
 ifstream f(argv[1]);vector<Entry>bank;string line;
 while(getline(f,line)){istringstream is(line);string tag;Entry e;is>>tag;if(tag!="STATE")continue;is>>e.order>>e.c>>e.n;for(int k=0;k<16;k++)is>>e.s.m[k]>>e.s.p[k];is>>e.s.p[16];bank.push_back(e);}
 sort(bank.begin(),bank.end(),[](auto&a,auto&b){return a.c<b.c;});
 for(int x=0;x<32;x++)for(int d=0;d<5;d++)nbs[x]|=1u<<(x^(1<<d));gen(0,1,0);for(int i=0;i<32;i++)for(auto r:rows)shifted[i].push_back(shift(r.m,i));
 int best=0,minC=999;uint64_t proposals=0,valids=0;
 for(int run=0;run<runs;run++){auto z=bank[rnd()%min(int(bank.size()),run%2?25:200)];auto order=z.order;gray[0]=0;int ix[16];for(int k=0;k<15;k++)gray[k+1]=gray[k]^(1<<(order[k]-'0'));for(int k=0;k<16;k++)ix[gray[k]]=k;for(int k=0;k<16;k++)for(int d=0;d<4;d++)adj[k][d]=ix[gray[k]^(1<<d)];
  auto s=z.s;auto old=eval(s);if(old.n!=z.n||old.c!=z.c)abort();State elite=s;int ecost=9999;float lambda=1.15f+4.5*uniform();int floor=run%3==0?193:188+rnd()%6;
  for(int t=0;t<steps;t++){
   float phase=float(t%500)/500,T=1.55*(1-phase)+0.05;auto n=s;int a=rnd()%16,kind=rnd()%100;
   int noise=10+rnd()%42;
   if(kind<51)bestMask(n,a,lambda,noise);
   else if(kind<67){int k=rnd()&1?0:16;n.p[k]=rnd()%32;bestMask(n,k?15:0,lambda,noise);}
   else{
    int b=min(15,a+1+int(rnd()%(kind<88?1:10)));if(b==a)--a;
    int u=rnd()%5,v=kind<92?u:rnd()%5,delta=rnd()%3?1<<(rnd()%5):rnd()%32;
    for(int k=a+1;k<=b;k++)n.p[k]=sx(n.p[k],u,v)^delta;
    for(int k=a+1;k<b;k++)n.m[k]=shift(axes(n.m[k],u,v),delta);
    n.m[a]=n.m[b]=0;if(rnd()&1)swap(a,b);bestMask(n,a,lambda,noise);bestMask(n,b,lambda,noise);
   }
   auto e=eval(n);proposals++;if(!e.c){valids++;if(e.n-1>best){best=e.n-1;writeBest(n,order,run,t);if(best>=192)return 0;}}
   if(e.n>=193&&e.c<minC){minC=e.c;cout<<"NEAR "<<run<<" "<<t<<" "<<e.n<<" "<<minC<<" "<<order<<endl;}
   auto cost=[&](E q){return lambda*q.c+max(0,floor-q.n)+0.2*max(0,193-q.n);};
   float gain=cost(old)-cost(e);if(gain>=0||uniform()<expf(gain/T)){old=e;s=n;}
   int score=4*e.c+2*max(0,193-e.n);if(score<ecost){elite=n;ecost=score;}
   if(t%500==499){s=rnd()%5?elite:z.s;old=eval(s);}
  }cout<<"RUN "<<run<<" "<<best<<" "<<minC<<" "<<proposals<<" "<<valids<<endl;
 }
}
