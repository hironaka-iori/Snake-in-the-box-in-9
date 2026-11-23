#include <fstream>
#define main exact_branch_program
#include "blocks.cpp"
#undef main
struct Walk{
 static constexpr int goal=193;
 int budget=0,visits=0,total=0,limit=0;bool unknown=false;P path,answer;array<int,512> alive{};
 bool grow(int v,int extra){
  if(++visits>limit){unknown=true;return false;}
  if(path.size()==goal){answer=path;return true;}
  P options;for(int w:nb[v])if(alive[w])options.push_back(w);
  int deg=options.size();if(!deg||extra<deg-1)return false;
  if(deg>1||path.size()==1){
   // All future vertices must be in the component of the current endpoint.
   array<char,512> seen{};array<int,512> queue{};queue[0]=v;seen[v]=1;int n=1,leaf=0,even=0;
   for(int i=0;i<n;i++){int z=queue[i],d=0;even+=!(popcount(unsigned(z))&1);
    for(int u:nb[z])if(alive[u]){d++;if(!seen[u]){seen[u]=1;queue[n++]=u;}}
    if(d<=1&&z!=v)leaf++;
   }
   int need=goal-path.size()+1;
   if(min(n-max(0,leaf-1),2*min(even,n-even)+1)<need)return false;
   extra=min(extra,n-need);if(extra<deg-1)return false;
  }
  alive[v]=0;for(int w:options)alive[w]=0;
  for(int w:options){alive[w]=1;path.push_back(w);if(grow(w,extra-deg+1))return true;path.pop_back();alive[w]=0;if(unknown)break;}
  alive[v]=1;for(int w:options)alive[w]=1;return false;
 }
 bool run(P cells,int lim){
  limit=lim;total=cells.size();budget=total-goal;
  for(int v:cells)alive[v]=1;P starts=cells;array<int,512> deg{};for(int v:cells)for(int w:nb[v])deg[v]+=alive[w];
  for(int x:cells)if(deg[x]==1){int last=-1,cur=x,n=0;
   while(deg[cur]<=2){n++;int next=-1;for(int u:nb[cur])if(alive[u]&&u!=last)next=u;if(next<0)break;last=cur;cur=next;}
   if(n>budget){starts={x};break;}
  }
  for(int v:starts){path={v};if(grow(v,budget))return true;if(unknown)return false;}return false;
 }
};
int main(int argc,char**argv){
 if(argc!=4)return 2;int limit=stoi(argv[3]);for(int v=0;v<512;v++)for(int d=0;d<9;d++)nb[v][d]=v^(1<<d);
 ifstream hostsfile(argv[1]),cases(argv[2]);string line;vector<P> hosts;while(getline(hostsfile,line)){istringstream f(line);P p;int v;while(f>>v)p.push_back(v);hosts.push_back(p);}
 int tested=0,unknown=0;long long nodes=0;
 while(getline(cases,line)){istringstream s(line);string state,tag;int row,cost,v;s>>state;if(state!="LIMIT"&&state!="AUDIT")continue;s>>row>>cost>>tag;P ext,p=hosts.at(row);while(s>>v){p.push_back(v);ext.push_back(v);}
  Walk w;if(w.run(p,limit)){cout<<"FOUND "<<row<<" vertices";for(int x:w.answer)cout<<" "<<x;cout<<endl;return 0;}
  nodes+=w.visits;unknown+=w.unknown;tested++;
  if(w.unknown){cout<<"LIMIT "<<row<<" "<<w.visits<<" outside";for(int x:ext)cout<<" "<<x;cout<<endl;}
 }
 cout<<"DONE checked "<<tested<<" unresolved "<<unknown<<" nodes "<<nodes<<endl;
}

