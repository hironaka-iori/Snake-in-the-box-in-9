#include <fstream>
#include <unordered_set>
#include <string>
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <utility>
#include <vector>
using namespace std;
unordered_set<string> forbidden;
bool eligible_path(const vector<int>& p){
 if(forbidden.empty())return true;
 const int len=142;
 for(int i=0;i+len<(int)p.size();i++){
    string key;
    for(int rev=0;rev<2;rev++){
       array<int,9> rename;rename.fill(-1);int next=0;string word;
       for(int h=0;h<len;h++){
          int j=i+(rev?len-1-h:h);
          int d=__builtin_ctz((unsigned)(p[j]^p[j+1]));
          if(rename[d]<0)rename[d]=next++;
          word+=char('0'+rename[d]);
       }
       if(!rev||word<key)key=word;
    }
    if(forbidden.count(key))return false;
 }
 return true;
}
struct Option{int on,off,score;};
struct Group{vector<int> scope;vector<Option> opts;int on=0,off=0,top=0;};
struct Change{int id,bit,old,sign;};
struct Search{
 vector<Group> g;array<vector<pair<int,int>>,512> refs;array<int,512> state{};
 vector<int> arm,path,assigned;vector<Change> changes;
 long long upper,threshold,nodes=0,cap;int target;
 bool fix(int v,int sign){
  if(state[v])return state[v]==sign;
  state[v]=sign;assigned.push_back(v);
  for(auto [i,b]:refs[v]){
   auto &f=g[i];changes.push_back({i,b,f.top,sign});(sign>0?f.on:f.off)|=b;
   int old=f.opts[f.top].score;
   while(f.top<(int)f.opts.size()&&((f.opts[f.top].on&f.off)||(f.opts[f.top].off&f.on)))f.top++;
   if(f.top==(int)f.opts.size())return false;
   upper+=f.opts[f.top].score-old;
   if(upper<threshold)return false;
  }
  return true;
 }
 void restore(size_t a,size_t b,long long score){
  while(changes.size()>a){
   auto c=changes.back();changes.pop_back();auto &f=g[c.id];
   f.top=c.old;(c.sign>0?f.on:f.off)&=~c.bit;
  }
  while(assigned.size()>b){state[assigned.back()]=0;assigned.pop_back();}
  upper=score;
 }
 bool visit(){
  if(upper<threshold||nodes>=cap)return false;
  nodes++;
  if(path.size()==target)return true;
  int tip=path.back(),prev=path.size()==1?-1:path[path.size()-2];
  for(int d=0;d<8;d++){
   int v=tip^(1<<d);if(state[v])continue;
   auto a=changes.size(),b=assigned.size();long long score=upper;bool ok=fix(v,1);
   for(int j=0;j<8&&ok;j++){
    int u=tip^(1<<j);if(u!=prev&&u!=v)ok=fix(u,-1);
   }
   if(ok){path.push_back(v);if(visit())return true;path.pop_back();}
   restore(a,b,score);if(nodes>=cap)break;
  }
  return false;
 }
  bool minimum=false; bool walk=false; int two_end_colour=-1; int shell_colour=0; vector<int> full_two;
 bool configurations(){
  if(nodes>=cap||upper<threshold)return false;
  nodes++;
  for(;;){
   size_t before=assigned.size();
   for(int side=0;side<2;side++){
    int delta=(arm.size()%2)+(two_end_colour==0?1:-1);
    int need=(target+int(side==shell_colour))/2;
    int known=0,unknown=0;
    for(int v=0;v<512;v++)if(__builtin_parity((unsigned)v)==side){
     known+=state[v]>0;unknown+=state[v]==0;
    }
    if((!minimum&&known>need) || known+unknown<need)return false;
    if(unknown && ((!minimum&&known==need) || known+unknown==need)){
     for(int v=0;v<512;v++)if(state[v]==0&&__builtin_parity((unsigned)v)==side)
      if(!fix(v,(!minimum&&known==need)?-1:1))return false;
    }
   }
   for(auto &f:g){
    int undecided=((1<<f.scope.size())-1)&~(f.on|f.off);
    if(!undecided)continue;
    int forceOn=undecided,forceOff=undecided;
    long long slack=upper-threshold;
    int best=f.opts[f.top].score;
    for(size_t j=f.top;j<f.opts.size()&&(forceOn||forceOff);j++){
     const auto &o=f.opts[j];
     if(best-o.score>slack)break;
     if((o.on&f.off)||(o.off&f.on))continue;
     forceOn&=o.on;forceOff&=o.off;
    }
    int forced=forceOn|forceOff;
    while(forced){int b=__builtin_ctz((unsigned)forced);forced&=forced-1;
     if(!fix(f.scope[b],forceOn&(1<<b)?1:-1))return false;
    }
   }
   if(upper<threshold)return false;
   if(assigned.size()==before)break;
  }
  if(walk){
   if((int)path.size()==target)return true;
   int tip=path.back(),prev=path.size()>1?path[path.size()-2]:-1;
   for(int axis=0;axis<8;axis++){
    int v=tip^(1<<axis);
    if(state[v]<0||find(path.begin(),path.end(),v)!=path.end())continue;
    size_t a=changes.size(),b=assigned.size();long long score=upper;
    bool ok=fix(v,1);
    for(int d=0;d<8&&ok;d++){
     int u=tip^(1<<d);
     if(u!=prev&&u!=v)ok=fix(u,-1);
    }
    if(ok){path.push_back(v);if(configurations())return true;path.pop_back();}
    restore(a,b,score);if(nodes>=cap)break;
   }
   return false;
  }
  vector<int> free;
  for(int v=0;v<512;v++)if(!state[v])free.push_back(v);
  if(free.empty()){
   int start=-1,ends=0;
   for(int v=0;v<512;v++)if(state[v]>0){
      int deg=0;for(int j=0;j<9;j++)deg+=state[v^(1<<j)]>0;
      if(deg==1){start=v;ends++;}if(deg<1||deg>2)return false;
   }
   if(ends!=2)return false;path.clear();int prev=-1;
   while(start>=0){path.push_back(start);int next=-1;
      for(int j=0;j<9;j++){int x=start^(1<<j);if(x!=prev && state[x]>0){next=x;break;}}
      prev=start;start=next;
   }
   if(!minimum)return int(path.size())==target;
   const int length=path.size();
   return length>=target && (length-target)%2==0
       && length==count(state.begin(),state.end(),1)
       && (!(length%2)||__builtin_parity((unsigned)path[0])==shell_colour);
  }
  int branch=free.front(),first=1;
  long long best=-1;
  for(int v:free){
   size_t a=changes.size(),b=assigned.size();long long score=upper;
   bool yes=fix(v,1);long long yp=score-upper;restore(a,b,score);
   bool no=fix(v,-1);long long np=score-upper;restore(a,b,score);
   if(!yes&&!no)return false;
   if(!yes||!no){if(!fix(v,yes?1:-1))return false;return configurations();}
   long long rank=8*min(yp,np)+max(yp,np);
   if(rank>best){best=rank;branch=v;first=yp<=np?1:-1;}
  }
  for(int side:{first,-first}){
   size_t a=changes.size(),b=assigned.size();long long score=upper;
   if(fix(branch,side)&&configurations())return true;
   restore(a,b,score);if(nodes>=cap)break;
  }
  return false;
 }

 void run(int id,int root,int scale,int fee,bool byCells){
  threshold=(long long)scale*target;long long sum=fee;for(auto &f:g)sum+=f.opts[0].score;
  if(sum!=upper)abort();shell_colour=root;state.fill(-1);
  for(int v:arm)state[v]=0;
  bool found=upper>=threshold&&configurations();
  cout<<id<<" "<<(found?"FOUND":nodes>=cap?"UNKNOWN":"EXHAUSTED")<<" "<<nodes;
  if(found)for(int v:path)cout<<" "<<v;
  cout<<endl;
 }
};
int main(int argc,char**argv){
 if(argc!=2&&argc!=3)return 2;int id;
 if(const char* file=getenv("Q9_AVOID_SHAPES")){
    ifstream in(file);string k;while(in>>k)forbidden.insert(k);
    if(forbidden.size()!=17974)return 5;
 }
 while(cin>>id){
  Search s;s.minimum=getenv("Q9_PATH_MINIMUM")!=nullptr;s.walk=argc==3 && string(argv[2])=="walk";if(argc==3&&string(argv[2])=="two0")s.two_end_colour=0;
  if(argc==3&&string(argv[2])=="two1")s.two_end_colour=1;
  s.cap=stoll(argv[1]);int root,scale,fee,n;
  cin>>s.target>>root>>scale>>fee>>s.upper>>n;s.arm.resize(n);for(int &v:s.arm)cin>>v;
  cin>>n;s.g.resize(n);
  for(int j=0;j<n;j++){
   int k;cin>>k;for(int a=0;a<k;a++){int v;cin>>v;s.refs[v].emplace_back(j,1<<a);s.g[j].scope.push_back(v);}
   cin>>k;s.g[j].opts.resize(k);for(auto &o:s.g[j].opts)cin>>o.on>>o.off>>o.score;
  }
  if(!cin)return 3;s.run(id,root,scale,fee,argc==3);
 }
}
