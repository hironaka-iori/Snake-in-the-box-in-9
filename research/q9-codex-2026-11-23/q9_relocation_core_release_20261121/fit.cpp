#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <queue>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
using P=vector<int>;using Perm=array<int,9>;
struct Pose{int row,j,dir,srcAxis,score,ok;Perm perm;};
struct Fit{
 int ep,y,axis,rank;array<bool,512>target{},forbid{};
 vector<P>&paths;mt19937 rng; vector<Pose> final[2];vector<int>best[2];int proposed=0;
 Fit(vector<P>&ps,int r,int e,int v):ep(e),y(v),axis(countr_zero((unsigned)(e^v))),rank(r),paths(ps),rng(84541+r){}
 pair<int,int> score(Pose&po,P*out=nullptr){
  auto &p=paths[po.row];int vertex=ep,good=target[ep],bad=forbid[ep];if(out)out->resize(p.size()),(*out)[po.j]=ep;
  for(int sign:{1,-1}){vertex=ep;for(int k=po.j+sign;k>=0&&k<(int)p.size();k+=sign){
   vertex^=1<<po.perm[countr_zero(unsigned(p[k]^p[k-sign]))];good+=target[vertex];bad+=forbid[vertex];if(out)(*out)[k]=vertex;
  }}
  po.ok=(bad==0);po.score=good-10*bad;return {good,bad};
 }
 void keep(Pose po,int type){
  if(!po.ok)return;
  for(auto &x:final[type])if(x.row==po.row&&x.j==po.j&&x.dir==po.dir&&x.perm==po.perm)return;
  auto &v=final[type];v.push_back(po);sort(v.begin(),v.end(),[](auto&a,auto&b){return a.score>b.score;});
  if(v.size()>10)v.pop_back();
 }
 void run(){
  vector<Pose> priority[2];for(int i=0;i<(int)paths.size();i++){auto&p=paths[i];
   for(int j=0;j<(int)p.size();j++)for(int dir:{1,-1}){int k=j+dir;if(k<0||k>=(int)p.size())continue;
    int source=countr_zero(unsigned(p[k]^p[j]));Perm perm;for(int z=0;z<9;z++)perm[z]=z;swap(perm[source],perm[axis]);
    Pose a{i,j,dir,source,0,0,perm};score(a);int endpoint=(k==0||k+1==(int)p.size());keep(a,endpoint);priority[endpoint].push_back(a);
   }}
  for(int type:{0,1}){auto&ps=priority[type];shuffle(ps.begin(),ps.end(),rng);stable_sort(ps.begin(),ps.end(),[](auto&a,auto&b){return a.score>b.score;});
   ps.resize(min(ps.size(),size_t(800)));for(Pose base:ps)for(int restart=0;restart<3;restart++){
    auto a=base;
    if(restart){for(int j=0;j<restart;j++){int u,v;do{u=rng()%9;v=rng()%9;}while(u==v||u==a.srcAxis||v==a.srcAxis);swap(a.perm[u],a.perm[v]);}score(a);}
    for(int step=0;step<8;step++){auto best=a;
     for(int u=0;u<9;u++)for(int v=u+1;v<9;v++)if(u!=a.srcAxis&&v!=a.srcAxis){Pose b=a;swap(b.perm[u],b.perm[v]);score(b);proposed++;if(b.score>best.score)best=b;if(b.ok&& (final[type].size()<10||b.score>final[type].back().score))keep(b,type);}
     if(best.score==a.score)break;a=best;
    }
   }
   for(auto&a:final[type]){P p;score(a,&p);cout<<rank<<" "<<type<<" "<<a.score<<" "<<a.row<<" "<<a.j<<" "<<a.dir;for(int v:p)cout<<" "<<v;cout<<'\n';}
  }
  cerr<<rank<<" evaluations "<<proposed<<" best_internal "<<(final[0].empty()?-1:final[0][0].score)<<" best_endpoint "<<(final[1].empty()?-1:final[1][0].score)<<endl;
 }
};
int main(){vector<P>bank;ifstream b("../q9_far189_spring_20261121/comparison191.words");string w;while(b>>w){P p={0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));bank.push_back(p);}
 ifstream b2("branches.txt");int r,ep,y,nb,nf;while(b2>>r>>ep>>y>>nb>>nf){Fit f(bank,r,ep,y);int v;while(nb--){b2>>v;f.forbid[v]=true;}while(nf--){b2>>v;f.target[v]=true;}f.run();}
}
