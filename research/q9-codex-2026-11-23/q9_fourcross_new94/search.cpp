#include <algorithm>
#include <array>
#include <bit>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <set>
#include <random>
#include <string>
#include <tuple>
#include <vector>
using namespace std;using P=vector<int>;using A=array<int,256>;
P readp(istream&in){int n;in>>n;P p(n);for(int&v:p)in>>v;return p;}
bool near(int x,int y){return popcount((unsigned)(x^y))==1;}
void mark(A&o,A&n,int x,int t){o[x]+=t;for(int d=0;d<8;d++)n[x^1<<d]+=t;}
struct Candidate{int score,seed,orient,sa,sb,ta,tb,L,lo,hi;P sec; auto rank()const{return make_tuple(score,hi-lo,seed,sa,orient);}};
struct S{
 vector<array<P,3>> src;vector<Candidate> all;P p,a,b,sec,br,q,full;A hu{},ha{},su{},sn{},pu{},pn{},ban{},exit{};int maxhole,maxsec,limit,total,seed,orient,sa,sb,ta,tb,L,h1,h2,best=0,budget,nodes;long long enumerated=0,opened=0,dfs=0,caps=0,feasible=0,upcalls=0;ofstream out;mt19937 rng{20261121};array<int,8> ord{0,1,2,3,4,5,6,7};
 S(string dest):out(dest){}
 void setup(){
  p=src[seed][0];a=src[seed][1];b=src[seed][2];if(orient){reverse(p.begin(),p.end());swap(a,b);}
  a.resize(a.size()-ta);b.resize(b.size()-tb);if(sa){p.insert(p.begin(),a[1]);a.erase(a.begin());}if(sb){p.push_back(b[1]);b.erase(b.begin());}
  hu={};ha={};for(int x:a)mark(hu,ha,x,1);for(int x:b)mark(hu,ha,x,1);
  exit={};for(int x=0;x<256;x++)exit[x]=!hu[x]&&!ha[x];
 }
 void candidate(){
  enumerated++;int f=p.size(),l=-1;for(int i=0;i<(int)p.size();i++){
   int x=p[i];bool bad=su[x]||sn[x]||(i&&i+1<(int)p.size()&&(hu[x]||(sa&&i>1&&(near(p.front(),x)||p.front()==x))||(sb&&i+2<(int)p.size()&&(near(p.back(),x)||p.back()==x))));
   if(bad){if(!i||i+1==(int)p.size())return;f=min(f,i);l=max(l,i);}
  }if(l<0){f=p.size()/2;l=f;}int h=f-1,k=l+1;if(k-h>maxhole||k-h<2)return;
  int baseline=L+(int)a.size()+(int)b.size()+(int)sec.size()+1; // full edges incl four crossings
  all.push_back({20*(192-baseline)+k-h,seed,orient,sa,sb,ta,tb,L,h,k,sec});
 }
 void gen(int left){
  int x=sec.back();if(sec.size()>=4&&exit[x])candidate();if(!left)return;
  for(int d=0;d<8;d++){int y=x^1<<d;if(hu[y]||su[y]||sn[y]!=1)continue;
   if((y==p.front())||(y==p.back())||near(y,p.front())||near(y,p.back()))continue;
   sec.push_back(y);mark(su,sn,y,1);gen(left-1);mark(su,sn,y,-1);sec.pop_back();
  }
 }
 void emit(){int e=full.size()-1;if(e<=best)return;best=e;for(int i=0;i<=e;i++)for(int j=i+1;j<=e;j++)if(full[i]==full[j]||near(full[i],full[j])!=(j==i+1))abort();out<<e<<" "<<seed<<" "<<L<<" "<<sec.size()-1;for(int v:full)out<<" "<<v;out<<endl;if(e>=192)cout<<"FOUND "<<e<<endl;}
 void extend(int left,bool flip){if(++upcalls>999999999999LL)return;emit();if(!left||best>=192)return;if(flip){reverse(full.begin(),full.end());extend(left,false);reverse(full.begin(),full.end());}
  int x=full.back()-256;for(int d:ord){int y=x^1<<d;if(hu[y]||ha[y]!=1||pu[y]||su[y])continue;mark(hu,ha,y,1);full.push_back(y+256);extend(left-1,flip);full.pop_back();mark(hu,ha,y,-1);if(best>=192)return;}
 }
 void got(){
  feasible++;q=P(p.begin(),p.begin()+h1+1);q.insert(q.end(),br.begin()+1,br.end());q.insert(q.end(),p.begin()+h2+1,p.end());
  full.clear();for(auto it=b.rbegin();it!=b.rend();it++)full.push_back(*it+256);for(auto it=q.rbegin();it!=q.rend();it++)full.push_back(*it);for(int v:a)full.push_back(v+256);for(int v:sec)full.push_back(v);full.push_back(sec.back()+256);
  mark(pu,pn,p[h2],1);mark(hu,ha,sec.back(),1);extend(8,true);mark(hu,ha,sec.back(),-1);mark(pu,pn,p[h2],-1);
 }
 void bridge(int left){
  if(best>=192||++nodes>budget)return;dfs++;int x=br.back(),tgt=p[h2];if(!left){if(x==tgt)got();return;}if(popcount((unsigned)(x^tgt))>left)return;
  for(int d:ord){int y=x^1<<d;if((y==tgt)!=(left==1))continue;
   if(y==tgt){br.push_back(y);if(pn[y]==(1+(h2+1<(int)p.size())))bridge(0);br.pop_back();continue;}if(pu[y]||ban[y]||pn[y]!=1)continue;mark(pu,pn,y,1);br.push_back(y);bridge(left-1);br.pop_back();mark(pu,pn,y,-1);if(nodes>budget||best>=192)break;
  }
 }
 void run(const Candidate&c,int pad){seed=c.seed;orient=c.orient;sa=c.sa;sb=c.sb;ta=c.ta;tb=c.tb;L=c.L;setup();sec=c.sec;h1=max(0,c.lo-pad);h2=min((int)p.size()-1,c.hi+pad);
  su={};sn={};for(int x:sec)mark(su,sn,x,1);ban={};for(int x=0;x<256;x++)ban[x]=su[x]||sn[x]||hu[x];
  pu={};pn={};P retained(p.begin(),p.begin()+h1+1);retained.insert(retained.end(),p.begin()+h2,p.end());for(int x:retained)mark(pu,pn,x,1);
  for(int j=0;j<(int)retained.size();j++)for(int i=0;i<j;i++)if(retained[i]==retained[j]||near(retained[i],retained[j])!=(i+1==j&&i!=h1))return;
  int len=L-((int)p.size()-1-(h2-h1));if(len<2||popcount((unsigned)(p[h1]^p[h2]))>len)return;
  // Remove target from near counts so its predecessor may be drawn. Forbid target's fixed neighbours separately.
  mark(pu,pn,p[h2],-1);br={p[h1]};nodes=0;opened++;bridge(len);caps+=nodes>budget;
 }
};
int main(int argc,char**argv){if(argc!=8)return 1;S s(string(argv[7])+".paths");s.maxhole=atoi(argv[1]);s.maxsec=atoi(argv[2]);int am=atoi(argv[3]),cap=atoi(argv[4]);s.budget=atoi(argv[5]);int pad=atoi(argv[6]);ifstream f("seeds.dat");int id;while(f>>id){array<P,3> rec;for(P&v:rec)v=readp(f);s.src.push_back(rec);}
 for(s.seed=0;s.seed<2;s.seed++)for(s.orient=0;s.orient<2;s.orient++)for(s.ta=0;s.ta<=am;s.ta++)for(s.tb=0;s.tb<=am;s.tb+=max(1,am/2))for(s.sa=0;s.sa<=1;s.sa++)for(s.sb=0;s.sb<=1;s.sb++){
  s.L=(s.sa+s.sb)%2?93:92;s.setup();s.su={};s.sn={};int x=s.a.back();if(x==s.p[0]||x==s.p.back()||near(x,s.p[0])||near(x,s.p.back()))continue;s.sec={x};mark(s.su,s.sn,x,1);s.gen(s.maxsec);
 }
 cout<<"generated "<<s.enumerated<<" candidates "<<s.all.size()<<endl;shuffle(s.all.begin(),s.all.end(),s.rng);stable_sort(s.all.begin(),s.all.end(),[](auto&a,auto&b){return a.rank()<b.rank();});int n=0;for(auto&c:s.all){if(++n>cap||s.best>=192)break;shuffle(s.ord.begin(),s.ord.end(),s.rng);for(int extra=0;extra<=pad;extra+=2){s.run(c,extra);if(s.best>=192)break;}}
 cout<<"done tested "<<min(n,cap)<<" routes "<<s.opened<<" calls "<<s.dfs<<" caps "<<s.caps<<" lower_solutions "<<s.feasible<<" upper_calls "<<s.upcalls<<" best "<<s.best<<endl;
}
