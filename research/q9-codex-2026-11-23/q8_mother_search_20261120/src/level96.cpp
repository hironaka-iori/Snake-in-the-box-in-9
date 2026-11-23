#include<algorithm>
#include<array>
#include<cassert>
#include<fstream>
#include<iostream>
#include<random>
#include<set>
#include<string>
#include<vector>
using namespace std;using P=vector<int>;mt19937 rng(19448);
string norm(const P&p,bool rev){int r[8];fill(r,r+8,-1);int cnt=0;string w;for(int k=1;k<p.size();k++){int i=rev?p.size()-k:k;int x=__builtin_ctz(p[i]^p[i-1]);if(r[x]<0)r[x]=cnt++;w+='0'+r[x];}return w;}
string can(const P&p){return min(norm(p,0),norm(p,1));}
bool verify(const P&p){for(int j=1;j<p.size();j++)for(int i=0;i<j;i++){int d=__builtin_popcount(unsigned(p[i]^p[j]));if(!d||((d==1)!=(j==i+1)))return false;}return true;}
int main(int argc,char**argv){set<string>seen;vector<P> queue;string w;
 auto read=[&](istream&in){while(in>>w)if(w.size()>=96){P p{0};for(char c:w)p.push_back(p.back()^1<<(c-'0'));if(seen.insert(can(p)).second)queue.push_back(p);}};read(cin);ifstream add(argv[1]);read(add);sort(queue.begin(),queue.end(),[](auto&a,auto&b){return a.size()>b.size();});int origin=queue.size(),news[102]{},proc=0;
 for(int ii=0;ii<queue.size()&&ii<stoi(argv[2]);ii++){
  P s=queue[ii];int n=s.size();int pos[256];fill(pos,pos+256,-1);for(int i=0;i<n;i++)pos[s[i]]=i;
  auto push=[&](const P&p,int move){auto key=can(p);if(seen.insert(key).second){assert(verify(p));queue.push_back(p);news[p.size()-1]++;cout<<norm(p,false)<<" "<<ii<<" "<<move<<" "<<can(s)<<endl;}};
  for(int w=0;w<256;w++)if(pos[w]<0){
   int nb[8],d=0;for(int k=0;k<8;k++)if(pos[w^(1<<k)]>=0)nb[d++]=pos[w^(1<<k)];if(d<1||d>3)continue;
   if(d==1&&(nb[0]==0||nb[0]==n-1)){P q=s;if(!nb[0])reverse(q.begin(),q.end());q.push_back(w);push(q,1);}
   int cand[28],cc=0;cand[cc++]=0;cand[cc++]=n-1;
   for(int h=0;h<d;h++)for(int t=-1;t<=1;t++)if(nb[h]+t>=0&&nb[h]+t<n)cand[cc++]=nb[h]+t;
   sort(cand,cand+cc);cc=unique(cand,cand+cc)-cand;
   for(int j=0;j<cc;j++){int del=cand[j];int olddeg=del!=0&&del!=n-1?2:1,links=d;bool good=true;
    for(int h=0;h<d;h++){if(nb[h]==del){links--;continue;}if(nb[h]!=0&&nb[h]!=n-1&&abs(nb[h]-del)!=1){good=false;break;}}
    if(!good||links!=olddeg)continue;
    auto adj=[&](int a,int b){return __builtin_popcount(unsigned(a^b))==1;};
    P q;
    if(!del||del==n-1){
     for(int i=0;i<n;i++)if(i!=del)q.push_back(s[i]);
     if(adj(q.front(),w))reverse(q.begin(),q.end());if(!adj(q.back(),w))continue;q.push_back(w);
    }else{
     P x(s.begin(),s.begin()+del),y(s.begin()+del+1,s.end());
     if(adj(x.front(),w))reverse(x.begin(),x.end());if(!adj(x.back(),w))continue;
     if(adj(y.back(),w))reverse(y.begin(),y.end());if(!adj(y.front(),w))continue;
     q=x;q.push_back(w);q.insert(q.end(),y.begin(),y.end());
    }
    push(q,0);
   }
  }
  proc++;
 }cerr<<"initial "<<origin<<" explored "<<proc<<" total "<<queue.size()<<" new96 "<<news[96]<<" new97 "<<news[97]<<" new98 "<<news[98]<<endl;}
