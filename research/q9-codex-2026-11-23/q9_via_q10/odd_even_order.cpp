// A Q9 even-length snake is specified by its ordered majority-parity vertices.
// For each consecutive pair, independently choose a common neighbor touched
// by exactly those two majority vertices. Then verify the resulting full path.
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
using Path=std::vector<int>;
std::array<std::vector<int>,512> two;
std::array<std::array<std::array<int,2>,512>,512> common;
int dist(int a,int b){return std::popcount(unsigned(a^b));}
bool valid(const Path&p){
  for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++)
    if(p[i]==p[j]||(dist(p[i],p[j])==1)!=(i==j+1))return false;
  return true;
}
struct Eval{
  int cost=0,bad=0;
  std::array<int,512> deg{},present{};
  std::vector<int> blocking;
  Eval(const Path&p){
    for(int v:p){
      if(present[v]++){cost=9999;return;}
      for(int d=0;d<9;d++)deg[v^(1<<d)]++;
    }
    for(int i=1;i<(int)p.size();i++){
      if(dist(p[i-1],p[i])!=2){cost=9999;return;}
      auto w=common[p[i-1]][p[i]];
      int c=std::min(deg[w[0]],deg[w[1]])-2;
      if(c){cost+=c;bad++;blocking.push_back(i);}
    }
    int low=10;for(int bit=1;bit<512;bit*=2)low=std::min(low,deg[p.back()^bit]);
    cost+=low-1;
  }
  Path restore(const Path&p){
    Path q{p[0]};for(int i=1;i<(int)p.size();i++){
      auto w=common[p[i-1]][p[i]];
      q.push_back(deg[w[0]]==2?w[0]:w[1]);q.push_back(p[i]);
    }
    int v=q.back();for(int bit=1;bit<512;bit*=2)if(deg[v^bit]==1){q.push_back(v^bit);break;}
    if(q.size()!=2*p.size()||!valid(q))throw 5;return q;
  }
};
struct Search{
  std::mt19937_64 rng;
  int rnd(int n){return rng()%n;}
  std::vector<Path> bank,near;
  Search(int seed):rng(seed){}
  bool propose(Path&q,const Eval& ev){
    int k=rnd(100),n=q.size(),i=rnd(n);
    if(!ev.blocking.empty()&&rnd(4)==0){
      int b=ev.blocking[rnd(ev.blocking.size())];i=b-rnd(2);
    }
    if(k<40){
      auto &opts=two[q[i?i-1:1]];int start=rnd(opts.size());
      for(int r=0;r<(int)opts.size();r++){
        int x=opts[(start+r)%opts.size()];
        if(!ev.present[x]&&(i+1==n||dist(x,q[i+1])==2)){q[i]=x;return true;}
      }return false;
    }
    if(k<56){
      if(rnd(2))std::reverse(q.begin(),q.end());
      auto&opts=two[q.back()];int v=opts[rnd(opts.size())];
      if(ev.present[v]&&v!=q.front())return false;
      q.erase(q.begin());q.push_back(v);return true;
    }
    if(k<76){
      if(i>=n-2)return false;
      int start=rnd(n-i-2);
      for(int t=0;t<n-i-2;t++){
        int j=i+2+(t+start)%(n-i-2);
        if(dist(q[i],q[j])==2&&(j+1==n||dist(q[i+1],q[j+1])==2)){
          std::reverse(q.begin()+i+1,q.begin()+j+1);return true;
        }
      }return false;
    }
    if(k<90){
      int a=rnd(9),b=(a+1+rnd(8))%9;
      int j=rnd(2)?n-1:std::min(n-1,i+1+rnd(35));
      if(j<n-1&&(((q[j]^q[i])>>a^(q[j]^q[i])>>b)&1))return false;
      for(int t=i+1;t<=j;t++)if((((q[t]^q[i])>>a)^((q[t]^q[i])>>b))&1)q[t]^=(1<<a)|(1<<b);
      return true;
    }
    int len=2+rnd(8);
    if(i+len>=n)return false;
    std::vector<int> moves;
    for(int j=i;j<i+len;j++)moves.push_back(q[j]^q[j+1]);
    if(rnd(2))std::shuffle(moves.begin(),moves.end(),rng);else{
      int a=rnd(len),b=rnd(len);
      int da=moves[a],db=moves[b];
      int c=1<<std::countr_zero(unsigned(da)),d=1<<std::countr_zero(unsigned(db));
      if(a==b||(da&d)||(db&c))return false;
      moves[a]^=c|d;moves[b]^=c|d;
    }
    for(int t=0;t<len;t++)q[i+t+1]=q[i+t]^moves[t];
    return true;
  }
  bool run(int epochs,int steps,double peak){
    int best=999;long long accepted=0,proposals=0;
    for(int epoch=0;epoch<epochs;epoch++){
      Path p=!near.empty()&&rnd(2)?near[rnd(near.size())]:bank[rnd(bank.size())];
      Eval ev(p);
      for(int s=0;s<steps;s++){
        if(ev.cost<best){best=ev.cost;std::cout<<"BEST "<<best<<" bad links "<<ev.bad<<std::endl;}
        if(!ev.cost){auto q=ev.restore(p);std::cout<<"FOUND "<<q.size()-1;for(int x:q)std::cout<<" "<<x;std::cout<<std::endl;return true;}
        Path q=p;if(!propose(q,ev)||q==p)continue;
        ++proposals;Eval next(q);int delta=next.cost-ev.cost;
        double temp=.08+peak*std::pow(1.-double(s)/steps,2);
        if(delta<=0||std::generate_canonical<double,53>(rng)<std::exp(-delta/temp)){
          p.swap(q);ev=std::move(next);++accepted;
          if(ev.cost==1&&rnd(20)==0){if(near.size()<5000)near.push_back(p);else near[rnd(near.size())]=p;}
        }
      }
      if(epoch%100==0)std::cout<<"CHECK "<<epoch<<" best "<<best<<" proposals "<<proposals<<" accepted "<<accepted<<std::endl;
    }
    std::cout<<"DONE best "<<best<<" proposals "<<proposals<<" accepted "<<accepted<<std::endl;return false;
  }
};
int main(int argc,char**argv){
  if(argc!=5)return 2;
  for(int v=0;v<512;v++)for(int a=0;a<9;a++)for(int b=0;b<a;b++){
    int u=v^(1<<a)^(1<<b);two[v].push_back(u);common[v][u]={v^(1<<a),v^(1<<b)};
  }
  Search s(std::stoi(argv[1]));std::string line;
  while(std::getline(std::cin,line)){std::istringstream in(line);int x;Path p,q;while(in>>x)p.push_back(x);
    if(p.empty())continue;if(p.size()%2)return 3;
    for(int i=0;i<(int)p.size();i+=2)q.push_back(p[i]);
    if(Eval(q).cost==9999)return 4;s.bank.push_back(q);
  }
  if(s.bank.empty())return 2;s.run(std::stoi(argv[2]),std::stoi(argv[3]),std::stod(argv[4]));
}
