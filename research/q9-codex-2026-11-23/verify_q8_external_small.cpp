#define Q8_AUDIT_LIBRARY
#include "verify_q8_clustered_hosts.cpp"
#include <random>
int main(){
 std::mt19937 rng(521192);vector<P> paths,sub;P p;
 auto collect=[&](auto&& self,int dim,vector<P>& bank)->void{
    bank.push_back(p);for(int d=0;d<dim;d++){
       int x=p.back()^(1<<d);bool ok=true;for(int j=0;j+1<p.size();j++)if(popcount(unsigned(p[j]^x))<=1)ok=false;
       if(ok){p.push_back(x);self(self,dim,bank);p.pop_back();}
    }
 };
 for(int x=0;x<16;x++){p={x};collect(collect,4,paths);}
 for(int x=0;x<8;x++){p={x};collect(collect,3,sub);}
 uint64_t yes[4]{},no[4]{};
 for(int i=0;i<900;i++){
    P a=sub[rng()%sub.size()],b=sub[rng()%sub.size()];int len=4+rng()%5;
    P h=a;for(int v:b)h.push_back(v+8);array<bool,16> inside{};for(int v:h)inside[v]=1;
    int needed=100;
    for(auto &w:paths)if(w.size()==len+1){int loss=0;for(int v:w)loss+=!inside[v];needed=min(needed,loss);}
    for(int e=0;e<=3;e++){
       int k=int(h.size())+e-len-1;Audit solver;solver.dim=4;bool ok=k>=0&&solver.run(h,len,k,e);
       assert((needed<=e)==ok);if(ok)yes[e]++;else no[e]++;
    }
 }
 for(int e=0;e<=3;e++)cout<<"MATCH "<<e<<" "<<yes[e]<<" "<<no[e]<<endl;
}
