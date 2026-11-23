#define main sibling_main
#include "../q9_change_basis/find.cpp"
#undef main
#ifdef CACHED_FILL
#include "cached_fill.hpp"
#else
#include "../q9_change_basis/forest.hpp"
#endif
using P=vector<int>;
struct Joint{
#ifdef CACHED_FILL
 CachedFill cached;
#endif
 Search raw;P dirs,pts;int T,t,h,lo,hi,baseid;long long cap,nodes=0,bases=0,runs=0;bool hit=false,unknown=false;Bits seenCandidate;
 Joint(P q,int goal,long long lim,int tag,int added):raw(q,goal),pts(q),T(goal),t(added-(goal+1-(int)q.size())),h(added),baseid(tag),cap(lim){lo=goal-2*h;hi=goal-h+9*t;}
 // Full retained forest has T-3 vertices minus one = T-3 edges at most, and at least T-6.
 bool contains(const P&rm,int x){return find(rm.begin(),rm.end(),x)!=rm.end();}
 P violation(const P&over,const P&rm){
    for(int v:over){if(contains(rm,v))continue;P q{v};for(int g:dirs){int y=v^g;if(raw.selected[y]&&!contains(rm,y)){q.push_back(y);if(q.size()==4)return q;}}}return {};
 }
 bool permitted(const P&over,P&rm){P v=violation(over,rm);if(v.empty())return true;if((int)rm.size()==t)return false;
    for(int x:v){rm.push_back(x);auto yes=permitted(over,rm);rm.pop_back();if(yes)return true;}return false;}
 void attempt(P&rm,int weight){int score=weight;for(int x:rm)for(int g:dirs)if(raw.selected[x^g])score--;for(int i=0;i<(int)rm.size();i++)for(int j=0;j<i;j++)if(find(dirs.begin(),dirs.end(),rm[i]^rm[j])!=dirs.end())score++;
    if(score<lo||score>T-h)return;runs++;
#ifdef CACHED_FILL
    bool found=cached.solve(dirs,pts,rm,T,baseid);
#else
    P remain;for(int x:pts)if(!contains(rm,x))remain.push_back(x);
    bool found=complete_forest(dirs,remain,T,baseid);
#endif
    if(found){hit=true;cout<<"EXTRA";for(int x:rm)cout<<" "<<x;cout<<endl;}}
 void choose(P&rm,int start,int weight){if(hit)return;if((int)rm.size()==t){attempt(rm,weight);return;}for(int j=start;j<(int)pts.size();j++){int x=pts[j];if(contains(rm,x))continue;rm.push_back(x);choose(rm,j+1,weight);rm.pop_back();if(hit)return;}}
 void allfixed(P&rm,const P&over,int weight){if(hit)return;P v=violation(over,rm);if(v.empty()){choose(rm,0,weight);return;}if((int)rm.size()==t)return;
    for(int x:v){rm.push_back(x);allfixed(rm,over,weight);rm.pop_back();if(hit)return;}}
 void dfs(const P&opts,int left,int sum,const Bits&once,const Bits&twice,const Bits&oldbad,const P&space){
    if(hit||unknown)return;if(++nodes>cap){unknown=true;return;}int n=opts.size();if(n<left)return;int min=sum,max=sum;
    for(int i=0;i<left;i++){min+=raw.edges[opts[i]];max+=raw.edges[opts[n-1-i]];}if(min>hi||max<lo)return;
    for(int j=0;j+left<=n;j++){int g=opts[j],score=sum+raw.edges[g];if(sum+left*raw.edges[g]>hi)break;if(left==1&&score<lo)continue;
      Bits bad=oldbad|(twice&raw.hits[g]);if((int)bad.count()>(11-left)*t)continue;
      dirs.push_back(g);P over,rm; if(bad.any()){for(int x:pts)if(bad[x])over.push_back(x);}
      if((left<=3||over.size()>=4)&&!permitted(over,rm)){dirs.pop_back();continue;}
      if(left==1){bases++;allfixed(rm,over,score);}
      else{Bits sp;P ext=space;for(int v:space){sp.set(v);sp.set(v^g);ext.push_back(v^g);}P follow;int mx=hi-score-(left-2)*raw.edges[g];auto two=twice|(once&raw.hits[g]);
        for(int k=j+1;k<n;k++){int y=opts[k];if(raw.edges[y]>mx)break;if(!sp[y]&&(int)(bad|(two&raw.hits[y])).count()<=(12-left)*t)follow.push_back(y);}
        dfs(follow,left-1,score,once^raw.hits[g],two,bad,ext);}
      dirs.pop_back();if(hit||unknown)return;
    }
 }
};
#ifndef NO_JOINT_MAIN
int main(int argc,char**argv){if(argc<3||argc>4)return 2;int added=argc==4?atoi(argv[3]):3;if(added<1||added>3)return 2;int T=atoi(argv[1]);long long cap=atoll(argv[2]);int id=0;string line;while(getline(cin,line)){istringstream f(line);string marker;f>>marker;if(marker!="points")return 3;P p;int x;Bits b;while(f>>x){if(x<0||x>=512||b[x])return 4;b.set(x);p.push_back(x);}Joint s(p,T,cap,id,added);if(s.t<0||s.t>3)return 5;P opts(511);iota(opts.begin(),opts.end(),1);sort(opts.begin(),opts.end(),[&](int x,int y){return s.raw.edges[x]!=s.raw.edges[y]?s.raw.edges[x]<s.raw.edges[y]:x<y;});// The identity basis and a minimum-weight independent basis give immediate incumbent tests.
vector<int> identity(9),greedy;for(int i=0;i<9;i++)identity[i]=1<<i;Bits span;span.set(0);P space{0};
for(int g:opts){if(span[g])continue;greedy.push_back(g);int k=space.size();for(int i=0;i<k;i++){int x=space[i]^g;span.set(x);space.push_back(x);}if(greedy.size()==9)break;}
for(const P &basis:{identity,greedy}){s.dirs=basis;P bad,rm;int weight=0;for(int g:basis)weight+=s.raw.edges[g];if(weight<s.lo||weight>s.hi)continue;
for(int x:p){int d=0;for(int g:basis)d+=b[x^g];if(d>2)bad.push_back(x);}if(s.permitted(bad,rm))s.allfixed(rm,bad,weight);if(s.hit)break;}
s.dirs.clear();if(!s.hit)s.dfs(opts,9,0,Bits(),Bits(),Bits(),P{0});cout<<"R "<<id++<<" "<<(s.hit?"FOUND":s.unknown?"UNKNOWN":"CLOSED")<<" "<<s.nodes<<" "<<s.bases<<" "<<s.runs<<endl;if(s.hit)break;}}

#endif
