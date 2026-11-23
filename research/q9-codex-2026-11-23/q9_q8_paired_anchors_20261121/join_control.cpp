#define main main_full_frontier
#include "join.cpp"
#undef main
int main(){
 for(int v=0;v<512;v++){hood[v].set(v);for(int k=0;k<9;k++)hood[v].set(v^(1<<k));}
 ifstream ma("mothers.tsv"),se("best.tsv"),ra("warm.tsv");int i,r,z,t,m,n;string w;
 while(ma>>i>>r>>z>>t>>w)mothers.push_back(w);while(se>>i>>r>>m>>z>>n>>w)ids.push_back(m);
 mt19937 gen(64292);int row=0,tries=0,hits=0,changed=0,maxlen=0;long long placements=0,clear=0,lim=0;budget=10000;
 ofstream out("join_control.tsv");int L,H,lo,hi,u,v;string mp;while(tries<150&&ra>>i>>r>>L>>H>>lo>>hi>>u>>v>>mp>>w){int rid=row++;if(int(w.size())<105)continue;++tries;
 string req=mothers[ids[i]].substr(u,v-u);for(char&c:req)c=mp[c-'0'];int k=2+gen()%3,cut=5+gen()%(v-u-10-k),last=cut+k;
 auto p=makepath(w.substr(0,2*cut)),q=makepath(w.substr(2*last));vector<int>dist;
 for(int d=0;d<512;d++)if(!(popcount((unsigned)d)%2)&&popcount((unsigned)d)<=2*k)dist.push_back(d);shuffle(dist.begin(),dist.end(),gen);
 for(int d:dist){++placements;int pos=p.vs.back()^d;bool ok=true;for(int x:q.vs)if(p.forbidden[x^pos]){ok=false;break;}if(!ok)continue;++clear;
 goalInner.reset();for(int h=1;h<(int)q.vs.size();h++)goalInner|=hood[q.vs[h]^pos];goalblock=goalInner|hood[pos];Mask block;for(int j=0;j+1<(int)p.vs.size();j++)block|=hood[p.vs[j]];
 gap=req.substr(cut,k);linkword.clear();nodes=0;finalV=pos;if(dfs(p.vs.back(),0,block)){string sol=p.w+linkword+q.w;assert(!countbad(sol));for(int t=0;t<(int)req.size();t++)assert(sol[2*t]==req[t]||sol[2*t+1]==req[t]);out<<rid<<' '<<cut<<' '<<last<<' '<<sol<<'\n';++hits;changed+=sol!=w;maxlen=max(maxlen,(int)sol.size());break;}lim+=nodes>=budget;}
 }
 cout<<"real_inputs "<<tries<<" recovered "<<hits<<" different_solution "<<changed<<" longest_edges "<<maxlen<<" placements "<<placements<<" clear_placements "<<clear<<" DFS_nodes "<<calls<<" capped "<<lim<<endl;
}
