#include "../q9_seed_growth.hpp"
#include <iostream>
#include <sstream>
#include <string>
#include <random>
using namespace std;
struct Bounded:SeedGrow{
 int cap,best=0,bestoutside=0,bestlength=-1;bool cutoff=false;Path partial;
 mt19937 g;int pick(int n){return g()%n;}
 bool enough(bool left,bool right){
   array<bool,512> visited{};int q[512],head=0,tail=0,hostcount=0,outcount=0;
   auto add=[&](int x){if(!visited[x]&&!used[x]&&!blocked[x]&&(host[x]||outer<extra)){visited[x]=true;q[tail++]=x;if(host[x])hostcount++;else outcount++;}};
   if(left)for(int d=0;d<9;d++)add(line.front()^(1<<d));
   if(right)for(int d=0;d<9;d++)add(line.back()^(1<<d));
   while(head<tail){int x=q[head++];for(int d=0;d<9;d++)add(x^(1<<d));}
   return int(line.size())+hostcount+min(outcount,extra-outer)>=target+1;
 }
 bool dfs(bool left,bool right){
   if(nodes>=cap){cutoff=true;return false;}
   nodes++;
   if(lost>slack||minDelete(unhit)>slack-lost)return false;
   if(int(line.size())>best){
     best=line.size();bestoutside=outer;if(best>=189)partial.assign(line.begin(),line.end());
   }
   if(int(line.size())>=target+1){witness.assign(line.begin(),line.end());return true;}
   if(!left&&!right)return false;
   if((nodes%127==1)&&!enough(left,right))return false;
   array<int,9> a{},b{};
   int na=left?options(line.front(),a):10,nb=right?options(line.back(),b):10;
   bool front=na<nb||(na==nb&&pick(2));int tip=front?line.front():line.back(),n=min(na,nb);auto&v=front?a:b;
   auto before=unhit;array<pair<int,int>,9> ranks{};
   for(int i=0;i<n;i++){
     int y=v[i];occupy(y,1);cover(tip,1);
     int rank=4*lost+(host[y]?0:4)+pick(7);
     cover(tip,-1);occupy(y,-1);unhit=before;ranks[i]={rank,y};
   }
   sort(ranks.begin(),ranks.begin()+n);
   for(int i=0;i<n;i++){
     int y=ranks[i].second;occupy(y,1);cover(tip,1);
     if(front)line.push_front(y);else line.push_back(y);
     bool ok=dfs(left,right);if(front)line.pop_front();else line.pop_back();
     cover(tip,-1);occupy(y,-1);unhit=before;if(ok||cutoff)return ok;
   }
   cover(tip,1);bool ok=dfs(left&&!front,right&&front);cover(tip,-1);unhit=before;
   return ok;
 }
 bool start(const Path& hostlist,const Path&p,int goal,int e){
   dim=9;target=goal;extra=e;slack=int(hostlist.size())+extra-goal-1;
   for(int v:hostlist)host[v]=1;
   initClaws();for(int x:p){line.push_back(x);occupy(x,1);}
   for(int i=1;i+1<p.size();i++)cover(p[i],1);
   if(outer>extra)abort();
   return dfs(true,true);
 }
};
int main(int argc,char**argv){int goal=stoi(argv[1]),limitScale=stoi(argv[2]),row=0;
 string l;while(getline(cin,l)){istringstream is(l);int id,e,cap,tag,n,m;
   if(!(is>>id>>e>>cap>>tag>>n))return 2;vector<int>host(n);for(int&v:host)is>>v;is>>m;vector<int>p(m);for(int&v:p)is>>v;
   for(int i=0;i<m;i++)for(int j=0;j<i;j++)if(p[i]==p[j]||(popcount(unsigned(p[i]^p[j]))==1)!=(j+1==i))abort();
   Bounded s;s.cap=cap*limitScale;s.g.seed(id*31+e*53+tag);
   bool ok=s.start(host,p,goal,e);cout<<"ROW "<<row<<" "<<id<<" "<<e<<" "<<p.size()<<" "<<s.nodes<<" "<<s.cutoff<<" "<<s.best<<" "<<s.bestoutside<<" "<<ok<<'\n';
   if(s.best>=189){cout<<"PATH "<<row<<" "<<s.bestoutside;for(int v:s.partial)cout<<" "<<v;cout<<'\n';}
   row++;if(ok&&goal>=192){cout<<"FOUND "<<row-1<<endl;break;}
 }
}
