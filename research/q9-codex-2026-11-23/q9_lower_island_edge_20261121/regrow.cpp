#define main native_upstream_beam
#include "../q9_free_upper_split_donors_20261121/beam.cpp"
#undef main
#include <fstream>
#include <sstream>
struct Regrow{
 int id,limit,local,best=0;long long total=0,capped=0,queries=0;vector<int> pre,tail,answer;
 void dfs(Set allowed){
   if(local>=limit||best>=192)return;++local;++total;
   int n=pre.size()+tail.size()-1;int u=tail.back();
   if(n>best){best=n;answer=pre;for(int v:tail)answer.push_back(256+v);if(!valid(answer))abort();}
   Node q;q.avail=allowed;
   if(!capacity(q,u,best-n+1))return;
   vector<pair<int,int>> next;
   for(int k=0;k<8;k++){int x=u^1<<k;if(!q.avail.has(x))continue;int degree=0;for(int t=0;t<4;t++)degree+=__builtin_popcountll(q.avail.a[t]&nbr[x].a[t]);next.emplace_back(degree,x);}
   sort(next.begin(),next.end());
   for(auto [_,v]:next){Set a=q.avail;for(int t=0;t<4;t++)a.a[t]&=~nbr[u].a[t];a.del(u);a.add(v);tail.push_back(v);dfs(a);tail.pop_back();if(local>=limit||best>=192)break;}
 }
 void run(const vector<int>&p){
    best=p.size()-1;answer=p;int s=p.size()-1;while(s>0&&p[s-1]>=256)--s;
    pre.assign(p.begin(),p.begin()+s);if(pre.back()>=256||p[s]!=pre.back()+256)abort();
    for(int cut:{7,11,15,19,23,27,31,35,43,55,69}){
      int hold=max(1,(int)p.size()-s-cut);tail.clear();
      for(int i=s;i<s+hold;i++)tail.push_back(p[i]-256);
      Set validGrid;validGrid.a.fill(~0ULL);
      for(int v:pre){if(v<256){validGrid.del(v);continue;}v-=256;validGrid.del(v);for(int j=0;j<4;j++)validGrid.a[j]&=~nbr[v].a[j];}
      for(int i=0;i+1<hold;i++){int v=tail[i];validGrid.del(v);for(int j=0;j<4;j++)validGrid.a[j]&=~nbr[v].a[j];}
      validGrid.add(tail.back());local=0;++queries;dfs(validGrid);capped+=local>=limit;if(best>=192)break;
    }
 }
};
int main(int argc,char**argv){if(argc!=5)return 2;for(int v=0;v<256;v++){if(!__builtin_parity(unsigned(v)))parity.add(v);for(int k=0;k<8;k++)nbr[v].add(v^1<<k);}
 ifstream in(argv[1]);ofstream out(argv[2]);Regrow z;z.limit=stoi(argv[3]);int min=stoi(argv[4]);string line;int cases=0;
 while(getline(in,line)){istringstream s(line);int id,n,x;s>>id>>n;if(n<min)continue;vector<int> p;while(s>>x)p.push_back(x);z.id=id;z.run(p);out<<id<<' '<<z.best;for(int v:z.answer)out<<' '<<v;out<<endl;++cases;if(z.best>=192)break;}
 cout<<"inputs "<<cases<<" queries "<<z.queries<<" nodes "<<z.total<<" capped "<<z.capped<<endl;
}
