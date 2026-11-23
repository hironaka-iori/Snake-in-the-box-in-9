#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <chrono>
#include <iostream>
#include <numeric>
#include <sstream>
#include <set>
#include <vector>
using namespace std;
using Path=vector<int>;
bool valid(const Path&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||((popcount(unsigned(p[i]^p[j]))==1)!=(i==j+1)))return false;return true;}
struct Test{
 int best=0,trials=0,goal=192,mode=0,row=0;uint64_t visited=0;
 set<string> high;bool collect=false;Path inp,steps;array<int,16> base{},alt{};
 bool run(int h,int j,int a,int b){
  trials++;array<int,512> previous;previous.fill(-1);int left=0,x=0,z=0;previous[x]=0;Path seq{0};seq.reserve(inp.size()+1);
  for(int i=0;i<inp.size();i++){
   int axis=inp[i];int diff=(i>=a&&i<b?alt:base)[axis];if(!diff)continue;
   int last=x;x^=diff;z++;seq.push_back(x);left=max(left,1+previous[x]);
   for(int d=0;d<9;d++){int u=x^(1<<d);if(u!=last)left=max(left,1+previous[u]);}
   previous[x]=z;visited++;
   if(collect&&z-left>=190){string w,bestw;for(int reverse:{0,1}){array<int,9>m;m.fill(-1);int next=0;w.clear();
     for(int j=1;j<=190;j++){int k=reverse?z+1-j:z-190+j;int ax=countr_zero(unsigned(seq[k]^seq[k-1]));if(m[ax]<0)m[ax]=next++;w+=char(48+m[ax]);}
     if(bestw.empty()||w<bestw)bestw=w;}if(high.insert(bestw).second)cout<<"CLASS190 "<<bestw<<" row "<<row<<" hidden "<<h<<" exchange "<<j<<" range "<<a<<" "<<b<<" source_ending "<<i<<endl;}
   if(z-left<=best)continue;
   Path p(seq.begin()+left,seq.end());assert(valid(p));best=z-left;
   cout<<"BEST "<<best<<" row "<<row<<" hidden "<<h<<" exchange "<<j<<" range "<<a<<" "<<b<<" source_ending "<<i<<" vertices";for(int v:p)cout<<" "<<v;cout<<endl;
   if(best>=goal)return true;
  }return false;
 }
};
int main(int argc,char**argv){Test t;t.goal=stoi(argv[1]);t.mode=stoi(argv[2]);int maxrows=stoi(argv[3]);t.collect=argc>4;string l;
 while(t.row<maxrows&&getline(cin,l)){istringstream in(l);int d,a;in>>d;if(d!=10)return 2;Path p{0};t.inp.clear();while(in>>a){t.inp.push_back(a);p.push_back(p.back()^(1<<a));}assert(valid(p));
  int n=t.inp.size();
  if(t.mode==2||t.mode==3||t.mode==4){
   for(int h=0;h<10;h++){int bix=0;for(int i=0;i<10;i++)t.base[i]=i==h?0:1<<(bix++);
    vector<int> events;for(int i=0;i<n;i++)if(t.inp[i]==h)events.push_back(i);events.push_back(n);
    for(int j=0;j<10;j++)if(h!=j)for(int k=0;k<10;k++)if(k!=j&&k!=h){
     t.base[h]=t.base[j];t.alt=t.base;t.alt[h]=t.base[k];
     for(int a=0;a+1<events.size();a++){
      if(t.mode==2){if(t.run(h,10*j+k,events[a],n))goto done;}
      else if(t.mode==4){for(int b=a+1;b<events.size();b++)if(t.run(h,10*j+k,events[a],events[b]))goto done;}
      else for(int count:{1,2,3,4,6,9,13})if(a+count<events.size())if(t.run(h,10*j+k,events[a],events[a+count]))goto done;
     }
    }
   }t.row++;continue;
  }
  for(int h=0;h<10;h++){int k=0;for(int i=0;i<10;i++)t.base[i]=i==h?0:1<<(k++);
    for(int j=0;j<10;j++)if(h!=j){t.alt=t.base;swap(t.alt[h],t.alt[j]);
     if(t.mode==5){vector<int> events;for(int q=0;q<n;q++)if(t.inp[q]==h||t.inp[q]==j)events.push_back(q);events.push_back(n);for(int a=0;a+1<events.size();a++)for(int b=a+1;b<events.size();b++)if(t.run(h,j,events[a],events[b]))goto done;}
     if(t.mode==0){for(int a=0;a<n;a++)if(t.inp[a]==h||t.inp[a]==j){if(t.run(h,j,a,n))goto done;}}
     if(t.mode==1){for(int a=0;a<n;a++){for(int g:{6,12,24,48,72,96,120})if(a+g<n){if(t.run(h,j,a,a+g))goto done;}}}
    }
  }t.row++;
 }
 done:cout<<"DONE completed "<<t.row<<" templates "<<t.trials<<" transitions "<<t.visited<<" best "<<t.best<<endl;
}
