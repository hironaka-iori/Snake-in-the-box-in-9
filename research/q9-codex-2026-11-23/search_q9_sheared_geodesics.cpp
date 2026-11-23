// Translate one facet of Q9, then replace each affected crossing by a geodesic.
// Every retained original vertex is mandatory. Intermediate vertices must have
// no contacts with any other anchor or a previously assigned geodesic interior.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
#include <string>
using namespace std;
struct Gap{int a,b; vector<vector<int>> ways;};
struct Scan{
 array<int,512> contact{}, used{};
 vector<Gap> gaps;
 vector<int> anchors, order;
 vector<vector<int>> choice;
 long long nodes=0;
 int limit=200000;
 bool capped=false;
 void toggle(int x,int change){
  used[x]+=change;for(int d=0;d<9;d++)contact[x^(1<<d)]+=change;
 }
 void routes(Gap& g,int x,vector<int>& way){
  int diff=x^g.b;
  if(has_single_bit(unsigned(diff))){g.ways.push_back(way);return;}
  for(int m=diff;m;m&=m-1){
   int y=x^(m&-m);
   if(used[y]||contact[y]!=int(has_single_bit(unsigned(y^g.a)))+int(has_single_bit(unsigned(y^g.b))))continue;
   way.push_back(y);routes(g,y,way);way.pop_back();
  }
 }
 bool solve(int i){
  if(++nodes>limit){capped=true;return false;}
  if(i==order.size())return true;
  int best=i;size_t score=size_t(-1);
  auto fits=[&](const Gap& g,const vector<int>& way){
   for(int y:way)if(used[y]||contact[y]!=int(has_single_bit(unsigned(y^g.a)))+int(has_single_bit(unsigned(y^g.b))))return false;
   return true;
  };
  for(int j=i;j<order.size();j++){
   auto &g=gaps[order[j]];size_t available=0;
   for(const auto &way:g.ways)if(fits(g,way)&&++available>=score)break;
   if(!available)return false;
   if(available<score){score=available;best=j;}
  }
  swap(order[i],order[best]);
  int k=order[i];auto& g=gaps[k];
  for(auto& w:g.ways){
   bool ok=true;for(int y:w)if(used[y]||contact[y]!=int(has_single_bit(unsigned(y^g.a)))+int(has_single_bit(unsigned(y^g.b)))){ok=false;break;}
   if(!ok)continue;
   for(int y:w)toggle(y,1);choice[k]=w;if(solve(i+1))return true;
   for(int y:w)toggle(y,-1);if(capped)return false;
  }swap(order[i],order[best]);return false;
 }
 bool run(const vector<int>& v,int s,int e){
  anchors.assign(v.begin()+s,v.begin()+e+1);
  for(int x:anchors)toggle(x,1);
  for(int j=1;j<anchors.size();j++)if(!has_single_bit(unsigned(anchors[j]^anchors[j-1]))){
   Gap g{anchors[j-1],anchors[j],{}};vector<int>w;routes(g,g.a,w);
   if(g.ways.empty())return false;gaps.push_back(std::move(g));
  }
  order.resize(gaps.size());iota(order.begin(),order.end(),0);choice.resize(gaps.size());
  stable_sort(order.begin(),order.end(),[&](int i,int j){return gaps[i].ways.size()<gaps[j].ways.size();});
  if(!solve(0))return false;
  vector<int> q{anchors[0]};int k=0;
  for(int i=1;i<anchors.size();i++){
   if(!has_single_bit(unsigned(anchors[i]^anchors[i-1]))){auto&w=choice[k++];q.insert(q.end(),w.begin(),w.end());}
   q.push_back(anchors[i]);
  }
  for(int i=0;i<q.size();i++)for(int j=0;j<i;j++)if(q[i]==q[j]||has_single_bit(unsigned(q[i]^q[j]))!=(i==j+1))abort();
  cout<<"FOUND "<<q.size()-1;for(int x:q)cout<<' '<<x;cout<<endl;return true;
 }
};
int main(int argc,char** argv){
 if(argc!=4)return 2;int target=stoi(argv[1]),low=stoi(argv[2]),high=stoi(argv[3]);string w;
 uint64_t maps=0,candidates=0,capped=0;int rows=0;
 while(cin>>w){
  vector<int> orig{0};for(char c:w)orig.push_back(orig.back()^(1<<(c-'0')));int n=orig.size();
  for(int d=0;d<9;d++)for(int t=1;t<512;t++){
   int h=popcount(unsigned(t));if((t&(1<<d))||h<low||h>high)continue;maps++;
   vector<int>v(n),cost(n);
   array<int,512> when;when.fill(-1);int s=0;
   for(int j=0;j<n;j++){
    int x=orig[j];if((x>>d)&1)x^=t;v[j]=x;
    int prev=when[x];if(prev>=s)s=prev+1;
    for(int bit=0;bit<9;bit++){
     int i=when[x^(1<<bit)];if(i>=s&&i!=j-1)s=max(s,i+1);
    }
    when[x]=j;if(j)cost[j]=cost[j-1]+popcount(unsigned(v[j]^v[j-1]));
    for(int a=s;a<j&&cost[j]-cost[a]>=target;a++){
     // It suffices to try windows minimal at both ends for this threshold.
     if(cost[j]-cost[a+1]>=target||cost[j-1]-cost[a]>=target)continue;
#ifdef Q9_EXPORT_ANCHORS
     if(j-a+1>=130){cout<<rows<<" "<<d<<" "<<t<<" "<<a<<" "<<j;for(int z=a;z<=j;z++)cout<<" "<<v[z];cout<<"\n";}continue;
#endif
     candidates++;Scan test;if(test.run(v,a,j)){cout<<"PARAM "<<rows<<" "<<d<<" "<<t<<" "<<a<<" "<<j<<endl;return 0;}capped+=test.capped;if(test.capped){cout<<"CAPPED";for(int x:test.anchors)cout<<" "<<x;cout<<endl;}
    }
   }
  }
  ++rows;if(rows%10==0)cout<<"AT "<<rows<<" "<<maps<<" "<<candidates<<" "<<capped<<endl;
 }
 cout<<"DONE "<<rows<<" "<<maps<<" "<<candidates<<" "<<capped<<endl;
return 0;
}
