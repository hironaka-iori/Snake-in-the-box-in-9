// Fixed-length random walks. E=8*(duplicate pairs)+(nonconsecutive adjacent pairs).
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
struct Walk {
 int dim,E=0;
 vector<int> p;
 array<int,512> cnt{},near{};
 void edit(int v,int step){
  if(step<0)--cnt[v];
  E+=step*(8*cnt[v]+near[v]);
  if(step>0)++cnt[v];
  for(int d=0;d<dim;d++)near[v^(1<<d)]+=step;
 }
 Walk(int d,vector<int> path):dim(d),p(path){
  for(int v:p)edit(v,1);
  E-=int(p.size())-1;
 }
 void verify() const{
  int n=0;
  for(int j=1;j<int(p.size());j++)for(int i=0;i<j;i++){
   int h=popcount(unsigned(p[i]^p[j]));
   if(i+1==j&&h!=1)abort();
   if(h==0)n+=8;if(h==1&&i+1<j)++n;
  }
  if(n!=E)abort();
 }
};
struct Search{
 mt19937_64 g;
 int pick(int n){return g()%unsigned(n);}
 bool accept(int delta,double t){return delta<=0 || (g()>>11)*0x1p-53<exp(-delta/t);}
 bool move(Walk&w,double t){
  int L=w.p.size()-1,k=pick(100),i,j;
  if(k<24){
   if(pick(2))reverse(w.p.begin(),w.p.end());
   int x=w.p.front()^(1<<pick(w.dim)),y=w.p.back(),old=w.E;
   w.edit(y,-1);w.edit(x,1);
   if(accept(w.E-old,t)){w.p.pop_back();w.p.insert(w.p.begin(),x);return true;}
   w.edit(x,-1);w.edit(y,1);return false;
  }
  if(k<31){
   i=pick(L-2);j=i+2+pick(L-i-1);
   if(popcount(unsigned(w.p[i]^w.p[j]))==1 && (j==L||popcount(unsigned(w.p[i+1]^w.p[j+1]))==1)){
    reverse(w.p.begin()+i+1,w.p.begin()+j+1);return true;
   }
   return false;
  }
  vector<int> q;
  if(k<61){
   i=1+pick(L-1);j=i;
   if(w.p[i-1]==w.p[i+1])return false;
   q={w.p[i-1]^w.p[i]^w.p[i+1]};
  }else if(k<75){
   if(pick(2))reverse(w.p.begin(),w.p.end());
   j=L;i=L-pick(pick(5)?10:L);
   int a=1<<pick(w.dim),b=1<<pick(w.dim);if(a==b)return false;
   for(int z=i;z<=j;z++){int v=w.p[z]^w.p[i-1];q.push_back(w.p[z]^((bool(v&a)!=bool(v&b))?a|b:0));}
  }else{
   int span=min(L,2+pick(k<92?8:42));
   i=1+pick(L-span+1);j=i+span-2;
   vector<int> s;for(int z=i;z<=j+1;z++)s.push_back(w.p[z]^w.p[z-1]);
   if(k<90){int a=pick(span),b=pick(span);swap(s[a],s[b]);}
   else if(k<97){int a=1<<pick(w.dim),b=1<<pick(w.dim),u=w.p[i-1]^w.p[j+1];if(a==b||bool(a&u)!=bool(b&u))return false;for(int &x:s)if(x==a||x==b)x^=a^b;}
   else reverse(s.begin(),s.end());
   int x=w.p[i-1];for(int z=0;z<span-1;z++)q.push_back(x^=s[z]);
  }
  bool changed=false;int old=w.E;
  for(int z=i;z<=j;z++)if(q[z-i]!=w.p[z]){changed=true;w.edit(w.p[z],-1);}
  if(!changed)return false;
  for(int z=i;z<=j;z++)if(q[z-i]!=w.p[z])w.edit(q[z-i],1);
  if(accept(w.E-old,t)){copy(q.begin(),q.end(),w.p.begin()+i);return true;}
  for(int z=i;z<=j;z++)if(q[z-i]!=w.p[z])w.edit(q[z-i],-1);
  for(int z=i;z<=j;z++)if(q[z-i]!=w.p[z])w.edit(w.p[z],1);
  if(w.E!=old)abort();return false;
 }
};
int main(int argc,char**argv){
 if(argc!=7)return 2;int d=stoi(argv[1]),L=stoi(argv[2]),epochs=stoi(argv[3]),steps=stoi(argv[4]);
 Search s{mt19937_64(stoul(argv[5]))};double peak=stod(argv[6]);vector<vector<int>> seeds;string line;
 while(getline(cin,line)){istringstream in(line);vector<int> p;int x;while(in>>x){if(x<0||x>=1<<d)return 3;p.push_back(x);}if(p.empty())continue;Walk w(d,p);w.verify();if(w.E)return 4;seeds.push_back(p);}
 if(seeds.empty())return 5;int best=999;long long proposed=0,accepted=0,ones=0;
 for(int epoch=0;epoch<epochs;epoch++){
  auto p=seeds[s.pick(seeds.size())];if(s.pick(2))reverse(p.begin(),p.end());
  if(int(p.size())>L-2)p.resize(L-2-s.pick(4));
  Walk w(d,p);
  while(int(w.p.size())<=L){
   int val=99999,x=0;
   for(int a=0;a<d;a++){int y=w.p.back()^(1<<a),score=60*w.cnt[y]+10*w.near[y]+s.pick(15);if(score<val){val=score;x=y;}}
   w.p.push_back(x);w.edit(x,1);w.E--;
  }
  for(int it=0;it<steps;it++){
   if(!(it%8192))w.verify();
   if(w.E<best){best=w.E;cout<<"BEST "<<epoch<<" "<<it<<" "<<best<<endl;}
   if(!w.E){w.verify();cout<<"FOUND";for(int v:w.p)cout<<" "<<v;cout<<endl;return 0;}
   ones+=(w.E==1);double f=1-double(it%10000)/10000;
   accepted+=s.move(w,.07+peak*f*f);proposed++;
  }
  if(epoch%50==49)cout<<"CHECK "<<epoch+1<<" "<<proposed<<" "<<accepted<<" "<<ones<<" "<<best<<endl;
 }
 cout<<"DONE "<<proposed<<" "<<accepted<<" "<<ones<<" "<<best<<endl;
}
