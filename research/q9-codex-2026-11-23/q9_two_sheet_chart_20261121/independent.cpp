#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;using Bits=bitset<512>;
struct Probe{int x;vector<int> images;};
struct Cell{int src,dst;};
struct Check{
 vector<Probe> todo;long long nodes=0,poses=0,tested=0,hits=0;
 bool compatible(int x,int y,const vector<Cell>&cells){for(auto [a,b]:cells)if(popcount((unsigned)(x&a))!=popcount((unsigned)(y&b)))return false;return true;}
 bool rec(const vector<Cell>&cells){
   nodes++;int best=-1,bestcount=1000;vector<int>choice;
   for(int i=0;i<(int)todo.size();i++){
     int x=todo[i].x;bool rigid=true;for(auto c:cells)if((x&c.src)&&(x&c.src)!=c.src){rigid=false;break;}
     vector<int>valid;for(int y:todo[i].images)if(compatible(x,y,cells)){valid.push_back(y);if((rigid&&valid.size())||(!rigid&&int(valid.size())>=bestcount))break;}
     if(valid.empty())return false;
     if(!rigid&&(int)valid.size()<bestcount){bestcount=valid.size();best=i;choice=move(valid);}
   }
   if(best<0)return true;
   int x=todo[best].x;for(int y:choice){vector<Cell>next;for(auto [a,b]:cells){if(a&x)next.push_back({a&x,b&y});if(a&~x)next.push_back({a&~x,b&~y});}if(rec(next))return true;}
   return false;
 }
 bool window(const vector<int>&q,int axis,int start,int goal){
   ++tested;vector<int>a,b;int anchor=-1;vector<pair<int,int>>reduced;
   for(int j=start;j<=start+goal;j++){
      int x=q[j],p=(x&((1<<axis)-1))|((x>>(axis+1))<<axis),s=(x>>axis)&1;
      if(j>start&&s!=reduced.back().second&&anchor<0)anchor=p;
      reduced.emplace_back(p,s);(s?b:a).push_back(j-start);
   }
   if(a.empty()||b.empty())return true;
   // The zero sheet stays fixed even when it is much smaller.
   array<int,512>deg{},occ{};for(int i:a){int v=reduced[i].first;occ[v]++;for(int k=0;k<9;k++)deg[v^(1<<k)]++;}
   vector<Probe>P;for(int j:b){const int x=reduced[j].first;int need=(j>0&&!reduced[j-1].second)+(j<goal&&!reduced[j+1].second);
    Probe c{x^anchor,{}};for(int y=0;y<512;y++){
     if(occ[y]||deg[y]!=need)continue;
     if(j>0&&!reduced[j-1].second&&popcount((unsigned)(reduced[j-1].first^y))!=1)continue;
     if(j<goal&&!reduced[j+1].second&&popcount((unsigned)(reduced[j+1].first^y))!=1)continue;
     c.images.push_back(y);
    }if(c.images.empty())return false;P.push_back(move(c));}
   for(int k=8;k>=0;k--){++poses;todo.clear();bool fail=false;int root=anchor^(1<<k);for(auto &c:P){Probe probe{c.x,{}};int w=popcount((unsigned)c.x);for(int target:c.images)if(popcount((unsigned)(target^root))==w)probe.images.push_back(target^root);
      if(probe.images.empty()){fail=true;break;}todo.push_back(move(probe));}if(fail)continue;
      sort(todo.begin(),todo.end(),[](auto&a,auto&b){return a.images.size()<b.images.size();});if(rec({{511,511}}))return true;
   }return false;
 }
};
int main(int ac,char**av){if(ac!=5)return 2;int g=stoi(av[2]),which=stoi(av[3]),batch=stoi(av[4]);ifstream f(av[1]);string s;Check C;int row=0;long long windows=0;
 while(getline(f,s)){istringstream is(s);int dim,v;is>>dim;assert(dim==10);vector<int>q;while(is>>v)q.push_back(v);
  for(int k=0;k<10;k++)if(which<0||which==k)for(int beg=0;beg+g<(int)q.size();beg+=batch){
   int end=min(int(q.size())-1-g,beg+batch-1);windows+=end-beg+1;
   if(end>beg&&!C.window(q,k,end,g-(end-beg)))continue;
   for(int j=beg;j<=end;j++){if(C.window(q,k,j,g)){C.hits++;cout<<"W "<<row<<" "<<k<<" "<<j<<" "<<g<<'\n';}}
  }row++;
 }
 cout<<"DONE rows "<<row<<" target "<<g<<" windows "<<windows<<" tested "<<C.tested<<" root_choices "<<C.poses<<" partition_states "<<C.nodes<<" hits "<<C.hits<<endl;
}
