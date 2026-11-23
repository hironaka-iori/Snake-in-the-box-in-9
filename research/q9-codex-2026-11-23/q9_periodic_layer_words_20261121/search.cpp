#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
using Word=vector<int>;
using Perm=array<int,9>;
int cleanPrefix(const Word&w){array<int,512> blocked{};int v=0,n=0;auto mark=[&](int x){++blocked[x];for(int d=0;d<9;d++)++blocked[x^(1<<d)];};mark(0);for(int d:w){v^=1<<d;if(blocked[v]!=1)break;mark(v);++n;}return n;}
Word decode(const string&s){Word w;for(auto c:s)w.push_back(c-'0');return w;}
string str(const Word&w){string s;for(int v:w)s+='0'+v;return s;}
struct Period{int p,m,hits;};
vector<Period> periods(const Word&w){
 vector<Period> ps;for(int p=12;p<=80;p++){
  int score=0,den=0;for(int i=p;i<(int)w.size();i++){den++;score+=(w[i]==w[i-p]);}
  ps.push_back({p,den,score});
 }
 stable_sort(ps.begin(),ps.end(),[](auto a,auto b){return a.hits*b.m>b.hits*a.m;});return ps;
}
Perm fit(const Word&w,int p,int sep){
 int ct[9][9]={};for(int i=p;i<int(w.size());i++)if(w[i-p]!=sep&&w[i]!=sep)ct[w[i-p]][w[i]]++;
 int best[512],last[512]={};fill(best,best+512,-1);best[0]=0;
 for(int m=0;m<511;m++)if(best[m]>=0){int a=popcount(unsigned(m));for(int b=0;b<9;b++)if(!(m>>b&1)&&((a==sep)==(b==sep))){
  int n=m|(1<<b),v=best[m]+ct[a][b];if(v>best[n]){best[n]=v;last[n]=b;}
 }}
 int m=511;Perm f;for(int a=8;a>=0;a--){int b=last[m];f[a]=b;m^=1<<b;}return f;
}
struct Option{Word word;int source=-1,offset=-1,length=0,power=0,flip=0;};
struct Block{int start;Word word;vector<Option> variants;};
#include "ends.inc"
struct Search{
 const Word &word;int sep,p,gap,cap,mode,n,limit;Perm perm,inv;vector<Block> blocks;
 mt19937 &rng;array<int,512> blocked{};vector<int> point{0},choice,order,result;long long attempts=0,legal=0,donorOptions=0;int best=0,completeOrders=0;
 bool clipped=false;
 Search(const Word&w,int d,int period,int breaks,int budget,int m,int options,mt19937&r):word(w),sep(d),p(period),gap(breaks),cap(budget),mode(m),limit(options),rng(r){
  perm=fit(w,p,sep);for(int a=0;a<9;a++)inv[perm[a]]=a;
  int s=0;for(int i=0;i<=int(w.size());i++)if(i==int(w.size())||w[i]==d){blocks.push_back({s,Word(w.begin()+s,w.begin()+i),{}});s=i+1;}n=blocks.size();
  for(auto &b:blocks)variants(b);mark(0,1);
 }
 void variants(Block&b){
  set<Word> seen;vector<Option> raw;
  auto add=[&](Word u,int src,int at,int len){for(int power:{0,1,-1})for(int rev:{0,1}){
   Word z=u;if(power)for(auto &d:z)d=power==1?perm[d]:inv[d];if(rev)reverse(z.begin(),z.end());
   if(!seen.insert(z).second||cleanPrefix(z)!=int(z.size()))continue;
   Option v{z,src,at,len,power,rev};if(src<0)b.variants.push_back(v);else raw.push_back(v);
  }};
  add(b.word,-1,-1,0);
  vector<array<int,3>> candidates;
  for(int length:{1,2,3,5,8})for(int i=0;i+length<=int(b.word.size());i++)for(int sign:{-1,1}){
   int j=b.start+i+sign*p;if(j<0||j+length>int(word.size()))continue;
   candidates.push_back({i,j,length});
  }
  shuffle(candidates.begin(),candidates.end(),rng);
  for(auto [i,j,len]:candidates){
   Word u=b.word;bool usable=true;for(int k=0;k<len;k++){int d=word[j+k];if(d==sep){usable=false;break;}
    u[i+k]=(j<b.start+i?perm[d]:inv[d]);}
   if(!usable||u==b.word)continue;add(u,j,i,len);
   if(int(raw.size())>=limit)break;
  }
  shuffle(raw.begin(),raw.end(),rng);if(raw.size()>size_t(limit))raw.resize(limit);
  donorOptions+=raw.size();b.variants.insert(b.variants.end(),raw.begin(),raw.end());
  shuffle(b.variants.begin(),b.variants.end(),rng);
 }
 void mark(int v,int delta){blocked[v]+=delta;for(int d=0;d<9;d++)blocked[v^(1<<d)]+=delta;}
 bool step(int a){int v=point.back()^(1<<a);if(blocked[v]!=1)return false;mark(v,1);point.push_back(v);return true;}
 void undo(size_t sz){while(point.size()>sz){mark(point.back(),-1);point.pop_back();}}
 bool dfs(int used,int remaining){
  int k=order.size();if(k==n){completeOrders++;bool moved=false;for(int i=0;i<n;++i)if(order[i]!=i)moved=true;
   if(mode==1&&!moved)return false;if(mode==2&&remaining==gap)return false;result=point;return true;
  }
  int start=rng()%n;for(int u=0;u<n;++u){int j=(u+start)%n;if(used>>j&1)continue;
   auto &b=blocks[j];for(int id=0;id<int(b.variants.size());++id){
    auto&o=b.variants[id];if(!remaining&&o.source>=0)continue;
    if(++attempts>cap){clipped=true;return false;}size_t sz=point.size();bool ok=!k||step(sep);if(ok)for(int d:o.word)if(!step(d)){ok=false;break;}
    if(extraSearch)extraSearch->observe(point);
    if(ok){++legal;best=max(best,int(point.size())-1);order.push_back(j);choice.push_back(id);
     if(dfs(used|(1<<j),remaining-(o.source>=0)))return true;order.pop_back();choice.pop_back();}
    undo(sz);if(clipped)return false;
   }
  }return false;
 }
 void show(int row,int trial){
  cout<<"FOUND row "<<row<<" trial "<<trial<<" axis "<<sep<<" period "<<p<<" source "<<str(word)<<" perm";for(int x:perm)cout<<' '<<x;cout<<"\n";
  for(int z=0;z<n;z++){int j=order[z];auto&o=blocks[j].variants[choice[z]];cout<<"BLOCK "<<j<<" source "<<o.source<<" at "<<o.offset<<" size "<<o.length<<" power "<<o.power<<" flip "<<o.flip<<" word "<<str(o.word)<<"\n";}
  cout<<"PATH";for(auto v:result)cout<<' '<<v;cout<<endl;
 }
};
int main(int argc,char**argv){
 if(argc!=8)return 2;int trials=stoi(argv[1]),seed=stoi(argv[2]),cap=stoi(argv[3]),breaks=stoi(argv[4]),limit=stoi(argv[5]),mode=stoi(argv[6]),hi=stoi(argv[7]);mt19937 rng(seed);
 if(mode==3)extraSearch=new Ends();
 vector<Word>bank;string s;while(cin>>s)bank.push_back(decode(s));if(bank.empty())return 3;
 long long attempts=0,legal=0,donors=0;int viable=0,clipped=0,best=0;set<int> rs,axes,ps;int movedModel=0;
 for(int t=0;t<trials;t++){int row=rng()%bank.size();auto w=bank[row];auto lag=periods(w);int p=lag[rng()%min(6,int(lag.size()))].p;
  vector<int> split;for(int j=0;j<9;j++){int c=count(w.begin(),w.end(),j);if(c>=2&&c<=hi)split.push_back(j);}
  if(split.empty())continue;int d=split[rng()%split.size()];
  if(mode==1){vector<Word> parts(1);for(int x:w)if(x==d)parts.emplace_back();else parts.back().push_back(x);
   shuffle(parts.begin(),parts.end(),rng);w.clear();for(auto b:parts){if(!w.empty())w.push_back(d);if(rng()%2)reverse(b.begin(),b.end());w.insert(w.end(),b.begin(),b.end());}
   if(w.size()!=bank[row].size()||cleanPrefix(w)==int(w.size()))continue;p=periods(w)[0].p;
  }
  if(mode==2){int i=rng()%w.size();int e=rng()%9;if(w[i]==e||e==d||w[i]==d)continue;w[i]=e;if(cleanPrefix(w)==int(w.size()))continue;}
  Search h(w,d,p,breaks,cap,mode,limit,rng);viable++;rs.insert(row);axes.insert(d);ps.insert(p);bool ok=h.dfs(0,breaks);attempts+=h.attempts;legal+=h.legal;donors+=h.donorOptions;clipped+=h.clipped;best=max(best,h.best);
  if(ok){h.show(row,t);return 0;}
 }
 if(extraSearch){cout<<"ENDS seen "<<extraSearch->often<<" distinct189 "<<extraSearch->classes[0].size()<<" distinct190 "<<extraSearch->classes[1].size()<<" distinct191 "<<extraSearch->classes[2].size()<<" novel191 "<<extraSearch->novel<<endl;}
 cout<<"DONE trials "<<trials<<" built "<<viable<<" rows "<<rs.size()<<" axes "<<axes.size()<<" periods "<<ps.size()<<" tried "<<attempts<<" admissible "<<legal<<" donor_options "<<donors<<" capped "<<clipped<<" longest_full_blocks "<<best<<endl;return 0;
}
