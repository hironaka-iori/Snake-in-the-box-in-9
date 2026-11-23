#define main partial_prefix_main
#include "construct.cpp"
#undef main
using Mask=array<uint64_t,4>;
struct Arm{Mask m;P p;};
struct Matcher{
 Search search;array<vector<Arm>,256> groups;
 long long compared=0,avoided=0,placed=0,cycles=0,perms=0,donors=0;
 void load(const string&file,int floor,bool many){
    ifstream in(file);string w;set<string> known;
    while(in>>w)for(int rev=0;rev<2;rev++,reverse(w.begin(),w.end())){
      for(int n=floor;n<=(int)w.size();n++){if(n<92&&n%5!=0)continue;string t=w.substr(0,n);int m[8],nd=0;fill(m,m+8,-1);for(char& c:t){int x=c-'0';if(m[x]<0)m[x]=nd++;c='0'+m[x];}
        if(!known.insert(t).second)continue;Arm a{};a.p={0};for(char c:t){int v=a.p.back()^(1<<(c-'0'));a.p.push_back(v);a.m[v>>6]|=1ull<<(v&63);}
        groups[a.p.back()].push_back(move(a));++donors;
      }
    }
 }
 void one(P p,int a,int b,int stride,int slack,int row){
    auto& z=search;z.id=row;z.best2=z.best3=0;z.ans2.clear();z.ans3.clear();
    array<int,8> perm; iota(perm.begin(),perm.end(),0);int ix=0;
    do{
      if(ix++%stride)continue;++perms;
      int f[256]{},inv[256]{};for(int v=1;v<256;v++){f[v]=f[v&(v-1)]^(1<<perm[countr_zero(unsigned(v))]);inv[f[v]]=v;}
      for(int side=0;side<2;side++){z.low=p;if(side)reverse(z.low.begin(),z.low.end());z.s=z.low.front();z.e=z.low.back();
        for(int pick=0;pick<2;pick++){z.y=pick?b:a;z.z=pick?a:b;int target=f[z.y^z.s];
          fill(z.blocked,z.blocked+256,0);Mask forbid{};for(int v:z.low)if(v!=z.s){int q=f[v^z.s];forbid[q/64]|=1ull<<(q%64);z.blocked[v]=1;}
          {int q=f[z.z^z.s];forbid[q/64]|=1ull<<(q%64);}z.blocked[z.s]=z.blocked[z.y]=z.blocked[z.z]=1;
          auto attempt=[&](int end){
            auto& group=groups[end];compared+=group.size();
            for(auto& arm:group){
              if((arm.m[0]&forbid[0])|(arm.m[1]&forbid[1])|(arm.m[2]&forbid[2])|(arm.m[3]&forbid[3]))continue;
              if(end!=target && ((arm.m[target/64]>>(target%64))&1))continue;
              ++avoided;z.seed.clear();for(int v:arm.p){int x=inv[v]^z.s;z.seed.push_back(x);z.mark(x,1);}
              if(end==target){++placed;z.joined();}
              else{
                int last=z.seed.back();
                auto finish=[&](){if(z.adj[z.y]==1){z.mark(z.y,1);z.seed.push_back(z.y);++placed;z.joined();z.seed.pop_back();z.mark(z.y,-1);}};
                if(dist(last,z.y)==1)finish();
                else for(int j=0;j<8;j++){int v=last^1<<j;if(dist(v,z.y)==1&&z.can(v)){z.mark(v,1);z.seed.push_back(v);finish();z.seed.pop_back();z.mark(v,-1);}}
              }
              for(int x:z.seed)z.mark(x,-1);if(z.hit)return;
            }
          };
          attempt(target);
          if(slack>=1)for(int j=0;j<8;j++)attempt(target^1<<j);
          if(slack>=2)for(int j=0;j<8;j++)for(int k=0;k<j;k++)attempt(target^1<<j^1<<k);
          if(z.hit)break;
        }
        if(z.hit)break;
      }
      if(z.hit)break;
    }while(next_permutation(perm.begin(),perm.end()));
    for(auto v:{z.ans2,z.ans3})if(!v.empty()){z.out<<row<<' '<<v.size()-1;for(int x:v)z.out<<' '<<x;z.out<<endl;}
 }
};
#ifndef NO_CATALOGUE_MAIN
int main(int argc,char**argv){
 if(argc!=10)return 2;Matcher m;m.search.out.open(argv[3]);m.search.freecap=stoi(argv[8]);iota(m.search.order.begin(),m.search.order.end(),0);
 m.load(argv[1],stoi(argv[4]),true);int stride=stoi(argv[5]),slack=stoi(argv[6]),lo=stoi(argv[7]),hi=stoi(argv[9]);
 ifstream in(argv[2]);string w;int a,b,count=0;
 for(int i=0;in>>w>>a>>b;i++){if(i<lo||i>=hi)continue;P p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));m.one(p,a,b,stride,slack,i);count++;if(m.search.hit)break;}
 cout<<"rows "<<count<<" distinct_rooted_prefixes "<<m.donors<<" permutations "<<m.perms<<" mask_tests "<<m.compared<<" clean_prefixes "<<m.avoided<<" legal_bridges "<<m.placed<<" free_tail_nodes "<<m.search.tailnodes<<" capped_tails "<<m.search.tailcuts<<" hit192 "<<m.search.hit<<endl;
}

#endif
