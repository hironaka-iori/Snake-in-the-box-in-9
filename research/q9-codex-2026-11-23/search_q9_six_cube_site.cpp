#define main chain_unused
#include "search_q9_six_cube_chain.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=2)return 2;int target=atoi(argv[1]);
 for(int v=0;v<64;v++)for(int d=0;d<6;d++)nb[v]|=B(v^(1<<d));
 int n;long long cases=0,nodes=0;
 while(std::cin>>std::dec>>n){
  std::vector<M> mask(n);P cell(n),port(n+1,-1);int original=0;
  for(int i=0;i<n;i++){std::cin>>std::dec>>cell[i]>>std::hex>>mask[i];original+=pop(mask[i]);
   if(i>0){M common=mask[i-1]&mask[i];if(pop(common)!=1)return 3;port[i]=__builtin_ctzll(common);}
  }
  // Interior entry/exit coordinates are fixed by unchanged neighbor blocks;
  // changing the port is allowed when it is the other neighbor endpoint as well.
  for(int h=0;h<n;h++){
   M bad=0;for(int j=0;j<n;j++)if(j!=h && abs(j-h)>1){
    int d=pop(cell[h]^cell[j]);if(!d){M m=mask[j];bad|=m;while(m)bad|=nb[low(m)];}
    else if(d==1)bad|=mask[j];
   }
   int needed=target+1-original+pop(mask[h]);if(needed<=0 || needed>27)continue;
   M start=h?B(port[h]):~M(0),end=h+1<n?B(port[h+1]):~M(0);
   // The first/last original neighboring segment can reverse while the fixed
   // middle segments retain their entrances/exits. Consider both endpoints.
   auto ends=[&](M m){M q=m,e=0;while(q){int v=low(q);if(pop(nb[v]&m)<=1)e|=B(v);}return e;};
   if(h){
    start=ends(mask[h-1]);
    if(h>=2 && pop(mask[h-1])>1)start&=~B(port[h-1]);
   }
   if(h+1<n){
    end=ends(mask[h+1]);
    if(h+2<n && pop(mask[h+1])>1)end&=~B(port[h+2]);
   }
   for(M u=start;u;){int a=low(u);
    for(M z=end;z;){int b=low(z);if(a==b && needed>1)continue;
     M ban=bad;if(h)ban|=mask[h-1]&~B(a);if(h+1<n)ban|=mask[h+1]&~B(b);
     if(ban&(B(a)|B(b)))continue;cases++;
     P route{a};
     auto walk=[&](auto&&self,int v,M block)->void {
      nodes++;if(v==b){
       if((int)route.size()<needed)return;
       std::vector<M> newMasks=mask;newMasks[h]=0;for(int x:route)newMasks[h]|=B(x);
       P full;int oldport=-1;
       for(int j=0;j<n;j++){M m=newMasks[j];int next=-1;
        if(j+1<n){M common=m&newMasks[j+1];if(pop(common)!=1)return;next=__builtin_ctzll(common);}
        int v=oldport;if(v<0){M e=ends(m);if(pop(e)>1)e&=~B(next);if(!e)return;v=__builtin_ctzll(e);}
        while(true){full.push_back(64*cell[j]+v);m^=B(v);if(!m)break;M opts=m&nb[v];if(pop(opts)!=1)return;v=__builtin_ctzll(opts);}
        if(next>=0&&v!=next)return;oldport=next;
       }
       for(int j=0;j<(int)full.size();j++)for(int i=0;i<j;i++)if(full[i]==full[j]||((pop(full[i]^full[j])==1)!=(i+1==j)))return;
       std::cout<<"FOUND "<<full.size()-1;for(int x:full)std::cout<<" "<<x;std::cout<<std::endl;std::exit(0);
      }
      if(nb[v]&B(b) && route.size()+1<(unsigned)needed)return;
      M left=~block;M rr=B(v),fr=B(v);while(fr){M expand=0;while(fr)expand|=nb[low(fr)];fr=expand&left&~rr;rr|=fr;}
      if(!(rr&B(b)) || route.size()+pop(rr)-1<(unsigned)needed)return;
      M opts=nb[v]&~block;while(opts){int w=low(opts);route.push_back(w);self(self,w,block|nb[v]|B(v));route.pop_back();}
     };
     walk(walk,a,ban|B(a));
    }
   }
  }
 }
 std::cerr<<"free segment endpoint configurations "<<cases<<" search nodes "<<nodes<<std::endl;
}
