#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using V=vector<int>;
int wt(int v){return popcount(unsigned(v));}
bool clean(const V&p){if(p.empty())return false;for(int i=0;i<int(p.size());++i){if(p[i]<0||p[i]>511)return false;for(int j=0;j<i;++j){int d=wt(p[i]^p[j]);if(d==0||(d==1)!=(i==j+1))return false;}}return true;}
struct Maps {
 int n=0;array<int,9>axes{},pre{};array<V,9>ready,subsets;
 V relative;array<int,512> mapped{};long long nodes=0;int anchor=0;
 const array<int,512>&ban;int fixedMask=0;
 Maps(const V&suffix,const array<int,512>&forbid):ban(forbid){
  int all=0,assigned=0;for(int x:suffix){relative.push_back(x^suffix[0]);all|=relative.back();}
  while(assigned!=all){int choice=0,best=-1;for(int d=1;d<512;d*=2)if((all&~assigned)&d){int score=0;for(int v:relative)score+=!(v&~(assigned|d));if(score>best){best=score;choice=d;}}
   axes[n]=choice;pre[n]=assigned;for(int v:relative)if((v&choice)&&!(v&~(assigned|choice)))ready[n].push_back(v);
   for(int u=assigned;;u=(u-1)&assigned){subsets[n].push_back(u);if(!u)break;}assigned|=choice;n++;
  }
 }
 bool solve(int k,int free){
  nodes++;
  if(k==n)return true;
  bool triedUnused=false;
  for(int choices=free;choices;choices&=choices-1){
   int d=choices&-choices;
   if(!(fixedMask&d)){if(triedUnused)continue;triedUnused=true;}
   bool ok=true;for(int v:ready[k])if(ban[anchor^(mapped[v^axes[k]]|d)]){ok=false;break;}
   if(!ok)continue;
   for(int u:subsets[k])mapped[u|axes[k]]=mapped[u]|d;
   if(solve(k+1,free^d))return true;
  }
  return false;
 }
};
int main(){string line;long long cuts=0,orient=0,placements=0,nodes=0;int rows=0;
 while(getline(cin,line)){istringstream f(line);V p;int x;while(f>>x)p.push_back(x);if(p.empty())continue;
  for(int split=1;split<int(p.size());++split){
   V a(p.begin(),p.begin()+split),b(p.begin()+split,p.end());if(!clean(a)||!clean(b))continue;if(a.size()<b.size())swap(a,b);cuts++;
   array<int,512> ban{};auto mark=[&](int q,int delta){ban[q]+=delta;for(int d=1;d<512;d*=2)ban[q^d]+=delta;};
   for(int q:a)mark(q,1);
   for(int ra=0;ra<2;++ra){if(ra)reverse(a.begin(),a.end());
    for(int rb=0;rb<2;++rb){if(rb)reverse(b.begin(),b.end());orient++;Maps maps(b,ban);
     int tip=a.back();
     for(int d=1;d<512;d*=2){int mid=tip^d;if(ban[mid]!=1)continue;mark(mid,1);
      for(int e=1;e<512;e*=2){int q=mid^e;if(e==d||ban[q]!=1)continue;
       maps.anchor=q;maps.fixedMask=q^mid;for(int y:a)maps.fixedMask|=y^q;placements++;
       if(maps.solve(0,511)){V result=a;result.push_back(mid);for(int v:maps.relative)result.push_back(q^maps.mapped[v]);if(!clean(result))abort();cout<<"FOUND row "<<rows<<" split "<<split<<"\nPATH";for(int y:result)cout<<" "<<y;cout<<endl;return 0;}
      }mark(mid,-1);
     }
     nodes+=maps.nodes;if(rb)reverse(b.begin(),b.end());
    }
    if(ra)reverse(a.begin(),a.end());
   }
  }
  rows++;
 }cout<<"DONE rows "<<rows<<" cuts "<<cuts<<" orientations "<<orient<<" placements "<<placements<<" nodes "<<nodes<<endl;
}
