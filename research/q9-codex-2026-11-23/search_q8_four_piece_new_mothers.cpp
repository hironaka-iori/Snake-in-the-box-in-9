// Search for an induced path by moving both tails through independent cube isometries.
#include <algorithm>
#include <functional>
#include <fstream>
#include <set>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Mask=array<uint64_t,8>;
struct Copy{Mask points{},boundary{};array<int,9> image{};};
bool intersects(const Mask&a,const Mask&b){for(int i=0;i<8;i++)if(a[i]&b[i])return true;return false;}
void insert(Mask&m,int v){m[v/64]|=1ULL<<(v%64);}
bool valid(const vector<int>&p){for(size_t i=0;i<p.size();i++)for(size_t j=0;j<i;j++)if(p[i]==p[j]||((popcount((unsigned)(p[i]^p[j]))==1)!=(j+1==i)))return false;return true;}
int moved(int x,const array<int,9>&m){int y=0;while(x){y|=m[countr_zero((unsigned)x)];x&=x-1;}return y;}
struct Tail{
 int anchor,depths=0;array<char,512>bad{};array<int,512>mapped{};array<int,9>order{},prior{},im{},preferred{};array<vector<int>,9>ready;vector<int>rel;vector<Copy>opts;
 long long nodes=0;int cap; bool limited=false;
 Tail(const vector<int>&p,int l,int r,bool left,int limit):anchor(p[left?l:r]),cap(limit){
  for(int i=l;i<=r;i++){int x=p[i]^anchor;bad[x]=1;if(x)for(int d=0;d<8;d++)bad[x^1<<d]=1;}
  for(int i=left?0:r+1;i<(left?l:(int)p.size());i++)rel.push_back(p[i]^anchor);
  int seen=0,all=0;for(int x:rel)all|=x;
  while(seen!=all){int best=-1,score=-1;for(int d=0;d<8;d++)if((all&~seen)&1<<d){int n=0;
    for(int x:rel)n+=(x&~(seen|1<<d))==0;if(n>score){best=d;score=n;}}
   prior[depths]=seen;order[depths]=best;seen|=1<<best;
   for(int x:rel)if((x&1<<best)&&!(x&~seen))ready[depths].push_back(x);
   depths++;
  }
 }
 void visit(int h,int available){
  nodes++;if(h==depths){if((int)opts.size()>=cap){limited=true;return;}
   Copy z;z.image=im;for(int x:rel){int v=anchor^mapped[x];insert(z.points,v);insert(z.boundary,v);for(int d=0;d<8;d++)insert(z.boundary,v^(1<<d));}opts.push_back(z);return;
  }
  int bit=1<<order[h],before=prior[h];
  for(int f=available;f&&!limited;f&=f-1){
   int y=f&-f;im[order[h]]=y;
   for(int t=before;;t=(t-1)&before){mapped[t|bit]=mapped[t]|y;if(t==0)break;}
   bool ok=true;for(int x:ready[h])if(bad[mapped[x]]){ok=false;break;}
   if(ok)visit(h+1,available^y);
  }
 }
};
using Count=uint64_t;
struct Pivot {
  function<bool(const array<int,512>&)> accept;
  array<bool,512> bad{};
  array<int,9> axes{}; array<vector<int>,9> ready;
  array<int,512> mapped{};
  array<int,10> fact{1,1,2,6,24,120,720,5040,40320,362880};
  Count leaves=0, nodes=0;
  bool visit(int level,int free) {
    ++nodes;
    if(level==8){++leaves;return accept(mapped);}
    int axis=1<<axes[level];
    bool success=false;
    for(int x=free;x;x&=x-1){
      int image=x&-x;
      // Map all submasks newly determined by this assignment.
      int prior=0; for(int i=0;i<level;i++)prior|=1<<axes[i];
      for(int m=prior;;m=(m-1)&prior){mapped[m|axis]=mapped[m]|image;if(!m)break;}
      bool ok=true;
      for(int v:ready[level])if(bad[mapped[v]]){ok=false;break;}
      if(!ok){leaves+=fact[8-level];continue;}
      if(visit(level+1,free^image)){success=true;break;}
    }
    return success;
  }
  bool solve(const vector<int>&p,int cut){
    int c=p[cut];
    for(int i=0;i<=cut;i++){int u=p[i]^c;bad[u]=true;if(i<cut)for(int j=0;j<8;j++)bad[u^(1<<j)]=true;}
    vector<int> rel;for(size_t i=cut+1;i<p.size();i++)rel.push_back(p[i]^c);
    int assigned=0;
    for(int depth=0;depth<8;depth++){
      int high=-1,best=-1;
      for(int j=0;j<8;j++)if(!(assigned&(1<<j))){
        int score=0,avail=assigned|(1<<j);
        for(int v:rel)if((v&~avail)==0)++score;
        if(score>high){high=score;best=j;}
      }
      axes[depth]=best;assigned|=1<<best;
      for(int v:rel)if((v&~assigned)==0&&(v&(1<<best)))ready[depth].push_back(v);
    }
    return visit(0,255);
  }
};

string signature(const vector<int>&p){
 string w;for(int i=1;i<p.size();i++)w+=char('0'+countr_zero((unsigned)(p[i]^p[i-1])));
 auto norm=[](string s){array<int,9>m;m.fill(-1);int n=0;for(char &c:s){int a=c-'0';if(m[a]<0)m[a]=n++;c='0'+m[a];}return s;};
 string a=norm(w);reverse(w.begin(),w.end());return min(a,norm(w));
}
int main(int argc,char**argv){
 if(argc!=5)return 2; ifstream refs(argv[4]);set<string>known;string row;while(refs>>row)known.insert(row);if(known.size()!=726)return 9;long long oldHits=0,newHits=0;mt19937 rng(stoul(argv[1]));int runs=stoi(argv[2]),target=stoi(argv[3]);
 vector<vector<int>>bank;vector<vector<pair<int,int>>> errors;string line;
 while(getline(cin,line)){istringstream ss(line);vector<int>p;int x;while(ss>>x)p.push_back(x);if(p.size()!=target+1)continue;
 vector<pair<int,int>> bd;for(int i=0;i<=target;i++)for(int j=0;j+1<i;j++)if(popcount((unsigned)(p[i]^p[j]))<=1)bd.push_back({j,i});
 bank.push_back(p);errors.push_back(bd);}
 if(bank.empty())return 7;
 long long joins=0,nodes=0,mixed=0;
 for(int z=0;z<runs;z++){
 int id=rng()%bank.size();auto p=bank[id];int m=25+rng()%(target-49),u=5+rng()%(m-9),v=m+5+rng()%(target-m-9);
 bool legal=true;for(auto [i,j]:errors[id])if((j<=u)||(i>=u&&j<=m)||(i>=m&&j<=v)||(i>=v))legal=false;
 if(!legal)continue;vector<int>L(p.begin(),p.begin()+m+1),R(p.begin()+m,p.end());
 Tail lt(L,u,m,true,45),rt(R,0,v-m,false,45);lt.visit(0,255);rt.visit(0,255);
 if(lt.opts.empty()||rt.opts.empty())continue;
 for(int t=0;t<3;t++){auto l=lt.opts[rng()%lt.opts.size()],r=rt.opts[rng()%rt.opts.size()];auto q=p;
 for(int j=0;j<u;j++)q[j]=p[u]^moved(p[u]^p[j],l.image);
 for(int j=v+1;j<=target;j++)q[j]=p[v]^moved(p[v]^p[j],r.image);
 if(target>=192&&q==p)continue;mixed+=(q!=p);Pivot solver;joins++;
 solver.accept=[&](const array<int,512>&mat){auto s=q;for(int j=m+1;j<=target;j++)s[j]=q[m]^mat[q[j]^q[m]];if(known.count(signature(s))){oldHits++;return false;}return true;};
 if(solver.solve(q,m)){for(int j=m+1;j<=target;j++)q[j]=q[m]^solver.mapped[q[j]^q[m]];
 if(!valid(q))abort();newHits++;known.insert(signature(q));cout<<"NEW "<<target<<" vertices";for(int y:q)cout<<" "<<y;cout<<endl;
 for(int j=0;j<2;j++,reverse(q.begin(),q.end()))for(int b=0;b<8;b++){auto w=q;w.push_back(q.back()^(1<<b));if(valid(w)){cout<<"FOUND "<<target+1<<" vertices";for(int y:w)cout<<" "<<y;cout<<endl;break;}}}
 nodes+=solver.nodes;
 }
 if(z%10000==0)cout<<"STEP "<<z<<" joins "<<joins<<" nodes "<<nodes<<endl;
 }
 cout<<"DONE joins "<<joins<<" known_hits "<<oldHits<<" new_hits "<<newHits<<" changed "<<mixed<<" nodes "<<nodes<<endl;
}


