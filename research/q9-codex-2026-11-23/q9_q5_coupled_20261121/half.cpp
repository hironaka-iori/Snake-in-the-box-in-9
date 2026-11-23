#define main anneal_main
#include "coupled.cpp"
#undef main
struct Partial{State st;int l=0,h=0,sz=0;float score=0;};
struct Row2{U m;int x,n;};
struct Core{array<U,4>m{};array<int,5>p{};int n=0;};
uint64_t visited=0,expanded=0,finished=0;
int globalbest=0;
U forbidden(const Partial&s,int j,int prev,int port){
 U block=0;for(int d=0;d<4;d++){int i=adj[j][d];if(i<s.l||i>s.h)continue;block|=s.st.m[i]&(i==prev?~(1u<<port):~0u);}return block;
}
void gen2(int x,U m,U ban,vector<Row2>&v){
 visited++;int n=popcount(m);v.push_back({m,x,n});
 for(U rem=nbs[x]&~(m|ban);rem;rem&=rem-1){int y=countr_zero(rem);gen2(y,m|(1u<<y),ban|nbs[x],v);}
}
int capped(U allowed,int root){
 if(root>=0&&!(allowed&(1u<<root)))return -70;
 int n=popcount(allowed);if(n>=25)return 14;
 U rr=root>=0?1u<<root:allowed;if(!rr)return 0;
 int best=0;while(rr){U front=rr&-rr,component=front;
   while(front){U nx=0;for(U s=front;s;s&=s-1)nx|=nbs[countr_zero(s)];front=nx&allowed&~component;component|=front;}
   int edges=0,eligible=0,ends=0;
   for(U s=component;s;s&=s-1){int i=countr_zero(s),degree=popcount(nbs[i]&component);if(degree>=2)eligible++;else ends++;}
   best=max(best,min(14,eligible+min(2,ends)));if(root>=0)break;rr&=~component;
 }return best;
}
int main(int argc,char**argv){
 if(argc!=7)return 2;vector<string>orders;ifstream a(argv[1]);string w;while(a>>w)orders.push_back(w);
 vector<Core>cores;ifstream f(argv[2]);while(f>>w){Core c;int k=0,x=0;c.p[0]=0;c.m[0]=1;c.n=w.size()+1;for(char ch:w){int d=ch-'0';if(d>=5){c.p[++k]=x;}else x^=1<<d;c.m[k]|=1u<<x;}c.p[4]=x;cores.push_back(c);}
 seed=stoul(argv[3]);int rounds=stoi(argv[4]),width=stoi(argv[5]),offset=stoi(argv[6]);
 for(int i=0;i<32;i++)for(int d=0;d<5;d++)nbs[i]|=1u<<(i^(1<<d));
 for(int r=0;r<rounds;r++){
  int id=(offset+37*r)%int(orders.size());auto order=orders[id];gray[0]=0;int ix[16];
  for(int k=0;k<15;k++)gray[k+1]=gray[k]^(1<<(order[k]-'0'));for(int k=0;k<16;k++)ix[gray[k]]=k;
  for(int k=0;k<16;k++)for(int d=0;d<4;d++)adj[k][d]=ix[gray[k]^(1<<d)];
  int start=4+rnd()%5;vector<Partial>beam;for(int z=0;z<width;z++){
   auto c=cores[rnd()%cores.size()];Partial s;s.sz=c.n;s.l=start;s.h=start+3;
   copy(c.m.begin(),c.m.end(),s.st.m.begin()+start);copy(c.p.begin(),c.p.end(),s.st.p.begin()+start);beam.push_back(s);}
  int local=0;for(int iter=0;iter<12&&!beam.empty();iter++){
   vector<Partial> next;int remain=11-iter;bool flip=rnd()&1;
   for(auto&s:beam){bool left=s.l>0&&(s.h==15||((iter%2)==flip));int j=left?s.l-1:s.h+1,root=left?s.st.p[s.l]:s.st.p[s.h+1];int prior=left?s.l:s.h;
    U no=forbidden(s,j,prior,root);if(no&(1u<<root))continue;vector<Row2>v;gen2(root,1u<<root,no,v);
    array<pair<float,int>,6> top;for(auto &t:top)t={-9999,-1};
    U conflict[16]{};int fixed[16]{};for(int d=0;d<4;d++){
      int z=adj[j][d];if(z>=s.l&&z<=s.h)continue;conflict[z]=forbidden(s,z,-1,0);
      if(z==s.l-1)conflict[z]=forbidden(s,z,s.l,s.st.p[s.l]),fixed[z]=s.st.p[s.l]+1;
      if(z==s.h+1)conflict[z]=forbidden(s,z,s.h,s.st.p[s.h+1]),fixed[z]=s.st.p[s.h+1]+1;
    }
    for(int vi=0;vi<(int)v.size();vi++){auto b=v[vi];float val=b.n+2.5*uniform();bool alive=true;
      for(int d=0;d<4;d++){int z=adj[j][d];if(z>=s.l&&z<=s.h)continue;bool tip=(left?z==j-1:z==j+1);
       U nk=b.m&(tip?~(1u<<b.x):~0u);U block=conflict[z]|nk;int port=tip?b.x:fixed[z]-1;
       if(port>=0&&(block&(1u<<port))){alive=false;break;}
       val-=0.14f*popcount(nk&~conflict[z]);if(port>=0){auto avail=nbs[port]&~block;if(!avail)val-=9;else val+=0.32f*popcount(avail);}
      }if(!alive)continue;int slot=0;for(int t=1;t<6;t++)if(top[t].first<top[slot].first)slot=t;if(val>top[slot].first)top[slot]={val,vi};
    }
    for(auto [vscore,vi]:top)if(vi>=0){
     auto b=v[vi];Partial t=s;t.st.m[j]=b.m;t.sz+=b.n;if(left){--t.l;t.st.p[j]=b.x;}else{++t.h;t.st.p[j+1]=b.x;}
     float rank=t.sz+3.8*uniform();for(int z=0;z<16;z++)if(z<t.l||z>t.h){
      int prev=z==t.l-1?t.l:(z==t.h+1?t.h:-1);int port=prev==t.l?t.st.p[t.l]:(prev==t.h?t.st.p[t.h+1]:-1);
      U banned=forbidden(t,z,prev,port<0?0:port);rank+=0.62f*capped(~banned,port)-0.1f*popcount(banned);
     }t.score=rank;next.push_back(t);expanded++;
     if(!remain){finished++;local=max(local,t.sz-1);if(t.sz-1>globalbest){globalbest=t.sz-1;writeBest(t.st,order,r,iter);if(globalbest>=192)return 0;}}
    }
   }
   auto cmp=[](const auto&a,const auto&b){return a.score>b.score;};if(next.size()>width){nth_element(next.begin(),next.begin()+width,next.end(),cmp);next.resize(width);}beam.swap(next);
  }cout<<"RUN "<<r<<" "<<id<<" "<<start<<" "<<local<<" "<<globalbest<<" "<<visited<<" "<<expanded<<" "<<finished<<endl;
 }
 return 0;
}
