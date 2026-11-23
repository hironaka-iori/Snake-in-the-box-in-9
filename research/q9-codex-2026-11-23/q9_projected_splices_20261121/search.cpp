#define main old_driver_unused
#include "../search_q9_projection_lifts.cpp"
#undef main
#include <fstream>
#include <bit>
#include <map>
#include <string>
using namespace std;
string canon(const Path&p){string best;for(int r=0;r<2;++r){int labels[256]={},next=1;string w;for(int t=1;t<(int)p.size();++t){int i=r?int(p.size())-t:t;int d=p[i]^p[i-1];if(labels[d]==0)labels[d]=next++;w.push_back('0'+labels[d]-1);}if(!r||w<best)best=w;}return best;}
string norm9(const Path&p){int m[512]={},next=1;string w;for(int i=1;i<(int)p.size();++i){int d=p[i]^p[i-1];if(!m[d])m[d]=next++;w.push_back('0'+m[d]-1);}return w;}
string code9(Path p){auto x=norm9(p);reverse(p.begin(),p.end());return min(x,norm9(p));}
struct Engine{
 int maxlen,kind,goal,lo,hi;long long bases=0,intervals=0,joins=0,simple=0,consistent=0,options=0,models=0;int best=0;set<string>seen,reference,classes;mt19937 rng;
 Engine(int cap,int k,int g,int seed):maxlen(cap),kind(k),goal(g),rng(seed){}
 int score(const Path&p,int floor,Path&out){Lift l(p);if(!l.prepare())return -1;++consistent;for(int z=l.base;z>=floor;--z){if(!l.search(0,l.base-z))continue;out=l.build();if((int)out.size()!=z+1||!valid(out,9))abort();models++;return z;}return -1;}
 void evaluate(const Path&p,int row,int axis,int i,int j,int reversed,int a,int b,int slide){
  Path witness;int z=score(p,goal-1,witness);if(z<goal-1)return;string key=code9(witness);
  bool emit=(z>best || (z==191 && !reference.count(key)&&classes.insert(key).second));best=max(best,z);
  if(emit||z>=goal){cout<<"WITNESS "<<z<<" row "<<row<<" axis "<<axis<<" i "<<i<<" j "<<j<<" reverse "<<reversed<<" axes "<<a<<" "<<b<<" translation "<<slide<<"\nPATH";for(int v:witness)cout<<" "<<v;cout<<endl;}
  if(z>=goal)exit(0);
 }
 void splice(const Path&q,int row,int axis){
  if(!seen.insert(canon(q)).second)return;++bases;
  int n=q.size();int total[256]={};for(auto x:q)++total[x];
  evaluate(q,row,axis,-1,-1,0,0,0,0);
  for(int i=1;i+1<n;++i){
   int inside[256]={};int out[256];copy(total,total+256,out);int duplicate=0;for(int x:out)duplicate+=max(0,x-1);
   for(int j=i;j<n-1&&j-i+1<=maxlen;++j){
    int u=q[j];if(++inside[u]>1)break;if(out[u]-->1)duplicate--;if(duplicate)continue;
    if(kind && j-i+1<2)continue;
    int a=0,b=0;if(kind){a=rng()%8;b=rng()%7;if(b>=a)b++;}int mask=(1<<a)|(1<<b);
    auto mapv=[&](int x){return ((((x>>a)^(x>>b))&1)!=0)?(x^mask):x;};
    ++intervals;
    for(int rev=0;rev<=(i!=j);++rev){
     int first=mapv(q[rev?j:i]),last=mapv(q[rev?i:j]);int delta=q[i-1]^first^last^q[j+1];if(popcount(unsigned(delta))>2)continue;
     for(int d=1;d<256;d*=2){
      if(popcount(unsigned(delta^d))!=1)continue;
      int t=q[i-1]^first^d;if(!t&&!rev&&!kind)continue;++joins;
      bool ok=true,changed=false;for(int k=i;k<=j;k++){int v=mapv(q[rev?i+j-k:k])^t;if(out[v]){ok=false;break;}changed|=v!=q[k];}
      if(!ok||!changed)continue;++simple;
      Path p=q;for(int k=i;k<=j;k++)p[k]=mapv(q[rev?j+i-k:k])^t;
      evaluate(p,row,axis,i,j,rev,a,b,t);
     }
    }
   }
  }
 }
 void final(){cout<<"DONE bases "<<bases<<" intervals "<<intervals<<" joins "<<joins<<" simple "<<simple<<" prepared "<<consistent<<" models "<<models<<" best "<<best<<" novel191 "<<classes.size()<<endl;}
};
#ifndef Q9_OMIT_SPLICE_MAIN
int main(int argc,char**argv){if(argc!=7)return 2;int cap=stoi(argv[1]),kind=stoi(argv[2]),goal=stoi(argv[3]),seed=stoi(argv[4]),limit=stoi(argv[5]);string mode=argv[6];Engine e(cap,kind,goal,seed);
 ifstream ref("q9_four_piece_191_classes.txt");string line;while(getline(ref,line))e.reference.insert(line);if(e.reference.size()!=131)return 4;
 int row=0;
 while(row<limit&&getline(cin,line)){istringstream f(line);Path p;int x;while(f>>x)p.push_back(x);if(p.empty())continue;
  if(mode=="seed"){for(int d=0;d<9;++d)e.splice(project(p,d),row,d);}
  else if(mode=="plant"){
   for(int d=0;d<9;++d){auto q=project(p,d);Path w;if(e.score(q,goal,w)<goal)continue;
    int size=q.size();for(int i=1;i+5<size;++i)for(int j=i+2;j<min(i+18,size-1);++j){
     for(int bit=1;bit<256;bit*=2){int tr=q[j]^bit^q[i-1];if(popcount(unsigned(q[i]^tr^q[j+1]))!=1)continue;
      auto damaged=q;for(int k=i;k<=j;k++)damaged[k]=q[i+j-k]^tr;
      if(set<int>(damaged.begin(),damaged.end()).size()!=damaged.size()||damaged==q)continue;if(e.score(damaged,goal,w)>=goal)continue;
      cout<<"PLANT original_axis "<<d<<" gap "<<i<<" "<<j<<" oldmax_below "<<goal<<"\nBASE";for(int u:damaged)cout<<" "<<u;cout<<endl;
      e.splice(damaged,0,d);return 7;
     }
    }
   }
  }else return 3;++row;
 }e.final();return 0;}

#endif
