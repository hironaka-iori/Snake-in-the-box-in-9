#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <deque>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using P=vector<int>;
string word(const P&p){string w;for(size_t i=1;i<p.size();i++)w+=char('0'+countr_zero(unsigned(p[i]^p[i-1])));return w;}
string normalized(string w){array<char,9> m{};char n='0';for(char& c:w){int d=c-'0';if(!m[d])m[d]=n++;c=m[d];}return w;}
string key(string w){string f=normalized(w);reverse(w.begin(),w.end());return min(f,normalized(w));}
void check(const P&p){for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||(popcount(unsigned(p[i]^p[j]))==1)!=(i==j+1))throw runtime_error("chord");}
struct Engine{
 array<int,512>use{},adj{};P A,B,mid,left,right;
 unsigned long long tries=0,bridgeNodes=0,joins=0,tipNodes=0,term=0,bridgeCuts=0,tipCuts=0;
 unsigned long long nodeCap=0,localNodes=0,localTips=0;
 int bound,best=0,goal;bool stopped=false;unordered_set<string> mids;string provenance;
 ofstream record;
 Engine(string file,int g):goal(g),record(file){}
 void mark(int v,int s){use[v]+=s;for(int i=0;i<9;i++)adj[v^(1<<i)]+=s;}
 void report(int n){
  best=n;P p(left.rbegin(),left.rend());p.insert(p.end(),A.begin(),A.end());p.insert(p.end(),mid.begin(),mid.end());p.insert(p.end(),B.begin(),B.end());p.insert(p.end(),right.begin(),right.end());check(p);
  record<<n<<" "<<word(p)<<" "<<provenance<<" "<<word(A)<<" "<<word(B)<<" "<<mid.size()<<endl;
  cout<<"BEST "<<n<<" "<<tries<<" "<<mids.size()<<endl;
 }
 void tips(int l,int r,bool side,int n){
  if(stopped)return;tipNodes++;if(++localTips>nodeCap){tipCuts++;return;}
  if(n>best)report(n);if(n>=goal){stopped=true;return;}
  if(side)tips(l,r,false,n);
  int v=side?l:r;auto &stack=side?left:right;
  for(int d=0;d<9&&localTips<=nodeCap&&!stopped;d++){int x=v^(1<<d);if(use[x]||adj[x]!=1)continue;mark(x,1);stack.push_back(x);tips(side?x:l,side?r:x,side,n+1);stack.pop_back();mark(x,-1);}
 }
 void join(){
  joins++;P p=A;p.insert(p.end(),mid.begin(),mid.end());p.insert(p.end(),B.begin(),B.end());
  if(!mids.insert(key(word(p))).second)return;localTips=0;tips(A.front(),B.back(),true,(int)p.size()-1);
 }
 void bridge(int tip){
  if(stopped)return;bridgeNodes++;if(++localNodes>nodeCap){bridgeCuts++;return;}
  int dist=popcount(unsigned(tip^B.front())),used=mid.size();
  if(dist==1){join();return;}if(used+dist-1>bound)return;
  for(int i=0;i<9&&localNodes<=nodeCap&&!stopped;i++){int x=tip^(1<<i);if(use[x])continue;
   bool touches=popcount(unsigned(x^B.front()))==1;
   if(adj[x]!=(touches?2:1))continue;
   mark(x,1);mid.push_back(x);bridge(x);mid.pop_back();mark(x,-1);
  }
 }
 void test(P a,P b,int maxBridge,string tag){
  if(stopped||a.empty()||b.empty())return;A=std::move(a);B=std::move(b);bound=maxBridge;provenance=tag;tries++;
  for(int v:A)mark(v,1);for(int v:B)mark(v,1);
  int cross=0;for(int v:B)for(int d=0;d<9;d++){int x=v^(1<<d);if(use[x])cross++;}
  cross-=2*(int(B.size())-1);
  if(cross==0||(cross==1&&popcount(unsigned(A.back()^B.front()))==1)){localNodes=0;bridge(A.back());}
  for(int v:A)mark(v,-1);for(int v:B)mark(v,-1);
 }
};
#ifndef TRIPOD_LIBRARY
int main(int argc,char**argv){
 if(argc!=8)return 2;
 string mode=argv[1];int trim=stoi(argv[2]),maxbridge=stoi(argv[3]),perclass=stoi(argv[4]),goal=stoi(argv[5]);Engine e(string(argv[7])+".records",goal);e.nodeCap=stoi(argv[6]);mt19937 rng(118037);
 ifstream file("arms.words");string line;int idx=-1;
 while(getline(file,line)&&!e.stopped){idx++;replace(line.begin(),line.end(),':',' ');istringstream row(line);array<P,3>arms;
  for(auto&a:arms){string w;row>>w;a={0};for(char c:w)a.push_back(a.back()^(1<<(c-'0')));}
  vector<array<int,8>>jobs;
  for(int removed=0;removed<3;removed++){
   P trunk=arms[(removed+1)%3];reverse(trunk.begin(),trunk.end());auto&other=arms[(removed+2)%3];trunk.insert(trunk.end(),other.begin()+1,other.end());auto& branch=arms[removed];
   if(mode=="cut"){
    // Release the branch completely, then release a second internal interval of the trunk.
    if(branch.size()-1>size_t(trim))continue;
    for(int l=0;l<=trim;l+=2)for(int r=0;l+r<=trim;r+=2)for(int gap:{1,2,3,4,6,8,12,16})
     for(int start=l+2;start+gap+2<int(trunk.size())-r;start++)
      for(int orient=0;orient<4;orient++)jobs.push_back({removed,l,r,start,gap,orient,0,0});
   }else{
    // Sever full third arm next to the centre; choose new orientations and four independent exposed ends.
    if(branch.size()<3)continue;
    for(int l=0;l<=trim;l++)for(int r=0;l+r<=trim;r++)for(int inner=2;l+r+inner-2<=trim&&inner<int(branch.size());inner++)
     for(int out=0;l+r+inner-2+out<=trim&&inner+out<int(branch.size());out++)for(int orient=0;orient<4;orient++)
      jobs.push_back({removed,l,r,inner,out,orient,0,0});
   }
  }
  shuffle(jobs.begin(),jobs.end(),rng);if(perclass&&int(jobs.size())>perclass)jobs.resize(perclass);
  for(auto j:jobs){auto [removed,l,r,h,k,orient,u,v]=j;
   P t=arms[(removed+1)%3];reverse(t.begin(),t.end());auto&o=arms[(removed+2)%3];t.insert(t.end(),o.begin()+1,o.end());P a,b;
   if(mode=="cut"){a.assign(t.begin()+l,t.begin()+h);b.assign(t.begin()+h+k,t.end()-r);}
   else{if(l+r>=int(t.size()))continue;a.assign(t.begin()+l,t.end()-r);auto&br=arms[removed];b.assign(br.begin()+h,br.end()-k);}
   if(orient&1)reverse(a.begin(),a.end());if(orient&2)reverse(b.begin(),b.end());
   string tag=to_string(idx)+","+to_string(removed)+","+to_string(l)+","+to_string(r)+","+to_string(h)+","+to_string(k)+","+to_string(orient);
   e.test(std::move(a),std::move(b),maxbridge,tag);if(e.stopped)break;
  }
 }
 cout<<"DONE classes "<<idx+1<<" attempted "<<e.tries<<" bridge_nodes "<<e.bridgeNodes<<" bridge_cap "<<e.bridgeCuts<<" joins "<<e.joins<<" distinct_middle "<<e.mids.size()<<" tips "<<e.tipNodes<<" tip_cap "<<e.tipCuts<<" best "<<e.best<<" hit "<<e.stopped<<endl;
}

#endif
