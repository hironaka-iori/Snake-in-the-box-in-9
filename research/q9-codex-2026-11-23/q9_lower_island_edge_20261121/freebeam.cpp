#include <set>
#include <numeric>
#define main native_upstream_beam
#include "../q9_free_upper_split_donors_20261121/beam.cpp"
#undef main
#include <fstream>
using Vec=vector<int>;
struct FreeBeam {
 int row,W,K,best=0;long long expansions=0,beams=0,pools=0,prunes=0;
 Vec answer,lower,link;int y,z,e,s;ofstream out;uint64_t randomSeed=0;
 void search_tail(Set avail){
   if(!avail.has(e))return;
   Node init;init.avail=avail;init.path[0]=e;int target=1+int(lower.size()+link.size());
   if(!capacity(init,e,max(1,best-target+1)))return;++beams;
   vector<Node> band{init};
   for(int depth=0;!band.empty();++depth){
     vector<Node> next;int n=target+depth+1;
     if(n>best){
       best=n;answer={z,y};for(auto it=link.rbegin();it!=link.rend();++it)answer.push_back(256+*it);
       answer.insert(answer.end(),lower.begin(),lower.end());for(int j=0;j<=depth;j++)answer.push_back(256+band[0].path[j]);
       if(answer.size()!=n+1||!valid(answer))abort();if(n>=192)return;
     }
     for(auto &a:band){int u=a.path[depth];for(int k=0;k<8;k++){int v=u^1<<k;if(!a.avail.has(v))continue;
       Node c=a;c.path[depth+1]=v;for(int j=0;j<4;j++)c.avail.a[j]&=~nbr[u].a[j];c.avail.del(u);c.avail.add(v);
       int hold=max(1,best-n+1);++expansions;int cap=capacity(c,v,hold);if(!cap){++prunes;continue;}
       int choices=0;for(int j=0;j<4;j++)choices+=__builtin_popcountll(c.avail.a[j]&nbr[v].a[j]);
       c.score=cap+double(gen()%1000)/85.+choices*1.2;next.push_back(c);
     }}
     if((int)next.size()>W){nth_element(next.begin(),next.begin()+W,next.end(),[](auto &a,auto &b){return a.score>b.score;});next.resize(W);}
     band.swap(next);
   }
 }
 void dfs(Set free,Set base,int maxlen,int& accepted){
   int u=link.back(),len=link.size()-1,d=__builtin_popcount(unsigned(u^y));
   if(d+len>maxlen||accepted>=K||best>=192)return;
   if(d==1){
      for(int i=0;i<(int)link.size()-1;i++)if(__builtin_popcount(unsigned(link[i]^y))<=1)return;
      link.push_back(y);for(int v:link){base.del(v);for(int j=0;j<4;j++)base.a[j]&=~nbr[v].a[j];}
      if(base.has(e)){++accepted;++pools;search_tail(base);}link.pop_back();return;
   }
   vector<int> ds(8);iota(ds.begin(),ds.end(),0);shuffle(ds.begin(),ds.end(),gen);
   for(int k:ds){int v=u^1<<k;if(!free.has(v)||v==y)continue;
      Set a=free;for(int j=0;j<4;j++)a.a[j]&=~nbr[u].a[j];a.del(u);a.add(v);link.push_back(v);dfs(a,base,maxlen,accepted);link.pop_back();if(accepted>=K||best>=192)break;}
 }
 void run(Vec l,int a,int b){best=0;answer.clear();
    for(int i=0;i<2;i++){lower=l;if(i)reverse(lower.begin(),lower.end());e=lower.back();s=lower.front();
      for(int j=0;j<2;j++){y=j?b:a;z=j?a:b;Set A;A.a.fill(~0ULL);for(int v:l)A.del(v);A.del(y);A.del(z);
        Set base=A;base.add(e);Set free=A;free.add(s);free.add(y);
        link={s};int d=__builtin_popcount(unsigned(y^s));
        for(int extra:{0,2,4,6}){int got=0;dfs(free,base,d+extra,got);if(best>=192)break;}
      }if(best>=192)break;
    }
    if(!answer.empty()){out<<row<<' '<<best;for(int v:answer)out<<' '<<v;out<<endl;}
 }
};
int main(int argc,char**argv){if(argc!=6)return 2;for(int v=0;v<256;v++){if(!__builtin_parity(unsigned(v)))parity.add(v);for(int k=0;k<8;k++)nbr[v].add(v^1<<k);}
 FreeBeam z;z.out.open(argv[3]);z.W=stoi(argv[4]);z.K=stoi(argv[5]);ifstream in(argv[1]),sel(argv[2]);set<int> ids;int t;while(sel>>t)ids.insert(t);string w;int a,b,ct=0;
 for(int i=0;in>>w>>a>>b;i++){if(!ids.count(i))continue;z.row=i;Vec p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));z.run(p,a,b);++ct;if(z.best>=192)break;}
 cout<<"cases "<<ct<<" sampled_bridges "<<z.pools<<" beams "<<z.beams<<" expanded "<<z.expansions<<" pruned "<<z.prunes<<" width "<<z.W<<endl;
}
