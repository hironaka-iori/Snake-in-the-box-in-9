// Jointly modify two true eight-dimensional paths rooted at 0. Overlapping
// projected vertices other than 0 are exactly the chords across the layers.
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using Path=std::vector<int>;
using Arms=std::array<Path,2>;
bool valid(const Path&p,int dim){
  std::vector<bool> used(1<<dim);
  for(size_t i=0;i<p.size();i++){
    int v=p[i];if(v<0||v>=1<<dim||used[v])return false;
    int edges=0;for(int k=0;k<dim;k++)edges+=used[v^(1<<k)];
    if(i&&(edges!=1||std::popcount(unsigned(v^p[i-1]))!=1))return false;
    used[v]=true;
  }
  return true;
}
int overlap(const Arms&p){
  std::array<bool,256> occ{};for(int v:p[0])occ[v]=true;
  int c=-1;for(int v:p[1])c+=occ[v];return c;
}
int length(const Arms&p){return p[0].size()+p[1].size()-1;}
Path joined(const Arms&p){
  Path q(p[0].rbegin(),p[0].rend());for(int x:p[1])q.push_back(x+256);return q;
}
Arms split(const Path&q){
  int cut=-1;
  for(int i=1;i<(int)q.size();i++)if((q[i]^q[i-1])==256){if(cut>=0)throw 1;cut=i;}
  if(cut<1)throw 2;
  Arms p;int root=q[cut-1]&255;
  for(int i=cut-1;i>=0;i--)p[0].push_back((q[i]&255)^root);
  for(int i=cut;i<(int)q.size();i++)p[1].push_back((q[i]&255)^root);
  if(!valid(p[0],8)||!valid(p[1],8))throw 3;
  return p;
}
struct Search{
  std::mt19937_64 gen;int best=0,bestnear=1000;long long trials=0,nodes=0;
  std::set<std::string> elite_keys, visited_valid;std::vector<Arms> bank;
  Search(int seed):gen(seed){}
  int rand(int n){return gen()%n;}
  double unit(){return std::generate_canonical<double,53>(gen);}
  std::string key(const Path&p){
    std::string best;
    for(int rev:{0,1}){
      std::array<int,256> label;label.fill(-1);int next=0;std::string s;
      for(int j=1;j<(int)p.size();j++){
        int i=rev?p.size()-j:j;
        int d=std::countr_zero(unsigned(p[i]^p[i-1]));
        if(label[d]<0)label[d]=next++;s+=char(label[d]);
      }
      if(best.empty()||s<best)best=s;
    }
    return best;
  }
  bool extend(Path p){
    if(p.size()>193||!valid(p,9))throw 7;
    if(p.size()==193){
      std::cout<<"FOUND";for(int x:p)std::cout<<" "<<x;std::cout<<std::endl;return true;
    }
    if(!visited_valid.insert(key(p)).second)return false;
    if(p.size()==192){
      std::cout<<"CLASS191";for(int x:p)std::cout<<" "<<x;std::cout<<std::endl;
    }
    std::array<bool,512> used{};for(int x:p)used[x]=true;
    for(int side=0;side<2;side++){
      std::reverse(p.begin(),p.end());
      for(int k=0;k<9;k++){
        int v=p.back()^(1<<k);if(used[v])continue;
        int deg=0;for(int i=0;i<9;i++)deg+=used[v^(1<<i)];
        if(deg==1){p.push_back(v);if(extend(p))return true;p.pop_back();}
      }
    }
    return false;
  }
  bool observe(const Arms&p){
    int L=length(p),c=overlap(p);
    if(c==0&&L>best||c==0&&L>=192){
      auto q=joined(p);if(!valid(q,9))throw 4;best=L;
      std::cout<<"VALID "<<L;for(int x:q)std::cout<<" "<<x;std::cout<<std::endl;
      if(L>=192)return true;
    }
    if(c==0&&L>=190&&extend(joined(p)))return true;
    if(L>=192&&c<bestnear){bestnear=c;std::cout<<"NEAR "<<L<<" "<<c<<std::endl;}
    if((L>=192&&c<=2||L>=190&&c==0)&&bank.size()<2500){
      auto q=joined(p);
      if(elite_keys.insert(key(q)).second)bank.push_back(p);
    }
    return false;
  }
  Path surgery(const Path&p,const Path&other,double penalty,int cap){
    const int n=p.size(), end=n-1;
    bool tail=rand(100)<33;
    int width=3+rand(std::min(53,end-2));
    int a=tail?end-width:rand(end-width+1), b=tail?end:a+width;
    int keep=tail?a:end-b+a;
    int minmid=std::max(1,(end-keep)-5);
    int maxmid=std::min(98-keep,(end-keep)+5);
    std::array<unsigned char,256> ban{},adj{},ocup{};
    for(int v:other)if(v)ocup[v]=1;
    for(int i=0;i<n;i++)if(i<a||i>b){
      int v=p[i];ban[v]=1;for(int d=0;d<8;d++)ban[v^(1<<d)]=1;
    }
    Path mid{p[a]},chosen;
    int visits=0;
    double bestweight=-1e9;
    std::array<int,8> order{0,1,2,3,4,5,6,7};std::shuffle(order.begin(),order.end(),gen);
    auto offer=[&](int edges,int c,bool addgoal){
      if(edges<minmid||edges>maxmid)return;
      double u=std::clamp(unit(),1e-12,1.0-1e-12);
      double weight=edges-penalty*c-0.7*std::log(-std::log(u));
      if(weight<=bestweight)return;bestweight=weight;chosen=mid;if(addgoal)chosen.push_back(p[b]);
    };
    auto dfs=[&](auto&&self,int c)->void{
      if(++visits>cap)return;
      int v=mid.back(),steps=mid.size()-1,dist=std::popcount(unsigned(v^p[b]));
      if(tail){offer(steps,c,false);if(steps>=maxmid)return;}
      else{
        if(dist==1){offer(steps+1,c+ocup[p[b]],true);return;}
        if(steps+dist>maxmid)return;
      }
      adj[v]++;for(int d=0;d<8;d++)adj[v^(1<<d)]++;
      int shift=rand(8);
      for(int t=0;t<8&&visits<cap;t++){
        int x=v^(1<<order[(shift+t)%8]);
        if(ban[x]||adj[x]!=1||(!tail&&x==p[b]))continue;
        mid.push_back(x);self(self,c+ocup[x]);mid.pop_back();
      }
      adj[v]--;for(int d=0;d<8;d++)adj[v^(1<<d)]--;
    };
    dfs(dfs,0);nodes+=visits;
    if(chosen.empty())return p;
    Path q(p.begin(),p.begin()+a);q.insert(q.end(),chosen.begin(),chosen.end());
    q.insert(q.end(),p.begin()+b+1,p.end());return q;
  }
  bool run(int rounds,int cap){
    std::vector<Arms> initial=bank;
    for(int r=0;r<rounds;r++){
      Arms p=(rand(4)==0?initial[rand(initial.size())]:bank[rand(bank.size())]);
      double cost=1.15+0.3*rand(8);
      for(int i=0;i<3000;i++){
        trials++;int side=rand(2);Arms q=p;
        if(rand(100)<5){
          auto& arm=q[side];
          if(rand(2)){
            std::reverse(arm.begin(),arm.end());int root=arm[0];for(int& v:arm)v^=root;
          }else{
            int a=rand(8),b=(a+1+rand(7))%8;
            for(auto& v:arm)if(((v>>a)^(v>>b))&1)v^=(1<<a)|(1<<b);
          }
        }else q[side]=surgery(p[side],p[1-side],cost,cap);
        if(q[side]==p[side])continue;
        if(!valid(q[side],8))throw 5;
        if(observe(q))return true;
        double delta=length(q)-length(p)-cost*(overlap(q)-overlap(p));
        double temp=0.12+0.8*(1.0-i/3000.0);
        if(delta>=0||unit()<std::exp(delta/temp))p.swap(q);
      }
      if(r%50==0)std::cout<<"CHECK "<<r<<" nodes "<<nodes<<" best "<<best<<" near "<<bestnear<<" bank "<<bank.size()<<std::endl;
    }
    std::cout<<"DONE "<<trials<<" proposals "<<nodes<<" nodes best "<<best<<" near "<<bestnear<<std::endl;
    return false;
  }
};
int main(int argc,char**argv){
  if(argc!=4)return 2; Search s(std::stoi(argv[1]));std::string line;
  while(std::getline(std::cin,line)){std::istringstream in(line);Path q;int x;while(in>>x)q.push_back(x);if(q.empty())continue;
    Arms p=split(q);s.bank.push_back(p);if(s.observe(p))return 0;}
  if(s.bank.empty())return 3;s.run(std::stoi(argv[2]),std::stoi(argv[3]));
}
