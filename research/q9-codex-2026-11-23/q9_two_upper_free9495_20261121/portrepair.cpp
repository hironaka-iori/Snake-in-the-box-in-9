#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;using P=vector<int>;using A=array<int,256>;
P path(string w,int x=0){P p{x};if(w!="-")for(char c:w)p.push_back(p.back()^(1<<(c-'0')));return p;}
struct Search{
 P low,arm,opp,lo,hi,fixedlo,fixedhi; A lu{},la{},hu{},ha{};int cap,nodes=0,ls,hs,goal,donor,dl,dh;long long runs=0,calls=0,caps=0,valid=0;set<string> uniq;ofstream out;bool found=false;Search(string nm):out(nm){}
 void mark(A&used,A&near,int v,int s){used[v]+=s;for(int j=0;j<8;j++)near[v^1<<j]+=s;}
 void save(){P q;for(int v:opp)q.push_back(v+256);reverse(q.begin(),q.end());for(auto i=low.rbegin();i!=low.rend()-dl;i++)q.push_back(*i);for(int i=1;i<(int)lo.size();i++)q.push_back(lo[i]);for(auto i=hi.rbegin();i!=hi.rend();i++)q.push_back(256+*i);for(int i=dh+1;i<(int)arm.size();i++)q.push_back(256+arm[i]);if((int)q.size()!=goal+1)abort();
  for(int j=0;j<(int)q.size();j++)for(int i=0;i<j;i++)if(q[i]==q[j]||(popcount((unsigned)(q[i]^q[j]))==1)!=(j==i+1))abort();
  string w;for(int i=0;i+1<(int)q.size();i++)w+=char(48+countr_zero((unsigned)(q[i]^q[i+1])));valid++;if(uniq.insert(w).second){out<<goal<<" "<<donor;for(int v:q)out<<" "<<v;out<<endl;}if(goal>=192)found=true;
 }
 void up(int left,int tgt){if(found||++nodes>cap)return;calls++;int v=hi.back();if(!left){if(v==tgt)save();return;}if(popcount((unsigned)(v^tgt))>left)return;for(int d=0;d<8&&nodes<=cap&&!found;d++){int x=v^1<<d;if(hu[x]||ha[x]!=1||(lu[x]&&x!=tgt)||(x==tgt)!=(left==1))continue;hi.push_back(x);mark(hu,ha,x,1);up(left-1,tgt);mark(hu,ha,x,-1);hi.pop_back();}}
 void down(int left){if(found||++nodes>cap)return;calls++;int v=lo.back();if(!left){if(!hu[v])up(hs,v);return;}for(int d=0;d<8&&nodes<=cap&&!found;d++){int x=v^1<<d;if(lu[x]||la[x]!=1||hu[x])continue;lo.push_back(x);mark(lu,la,x,1);down(left-1);mark(lu,la,x,-1);lo.pop_back();}}
 void run(int delta){ls=dl+delta;int old=low.size()+arm.size()+opp.size()-1;hs=dh+goal-old-delta;if(ls<1||hs<1||low.size()-1+delta<94||low.size()-1+delta>95)return;
   lo={low[dl]};hi={arm[dh]};lu={};la={};hu={};ha={};for(int i=dl;i<(int)low.size();i++)mark(lu,la,low[i],1);for(int i=dh;i<(int)arm.size();i++)mark(hu,ha,arm[i],1);for(int v:opp)mark(hu,ha,v,1);nodes=0;runs++;down(ls);caps+=nodes>cap;
 }
};
int main(int n,char**v){if(n!=6)return 2;int step=stoi(v[1]),mx=stoi(v[2]),cap=stoi(v[3]),goal=stoi(v[4]);Search s(string(v[5])+".paths");s.cap=cap;s.goal=goal;ifstream in("donors.words");vector<string>words;string w;while(in>>w)words.push_back(w);ifstream ar("direct.dat");int i;string a,b;set<int> seen;while(ar>>i>>a>>b){if(getenv("Q9_FIRST")&&!seen.insert(i).second)continue;s.donor=i;P raw=path(words[i]),arm=path(a),opp=path(b,raw.back());int total=raw.size()+arm.size()+opp.size()-1;vector<pair<int,int>> trims;if(getenv("Q9_PARITY_TRIM")){if((total^goal)&1)trims={{0,1},{1,0}};else trims={{0,0},{1,1},{2,0},{0,2}};}else trims={{0,0}};for(auto [x,y]:trims){if((int)arm.size()<=x||(int)opp.size()<=y)continue;s.low=raw;s.arm=P(arm.begin(),arm.end()-x);s.opp=P(opp.begin(),opp.end()-y);for(int rev=0;rev<2;rev++){for(s.dl=1;s.dl<=mx;s.dl+=step)for(s.dh=1;s.dh<=mx&&s.dh<(int)s.arm.size();s.dh+=step)for(int delta=-1;delta<=1;delta++){s.run(delta);if(s.found)goto done;}reverse(s.low.begin(),s.low.end());swap(s.arm,s.opp);}}}

 done:cout<<"goal "<<goal<<" windows "<<s.runs<<" nodes "<<s.calls<<" capped "<<s.caps<<" real "<<s.valid<<" distinct_oriented "<<s.uniq.size()<<endl;
}
