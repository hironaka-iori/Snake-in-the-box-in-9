#define main old_main
#include "search.cpp"
#undef main
struct Lower{
 P q,sec,head,tail,future;array<int,8> order; A occ{},nbr{};int goal,budget,nodes,nsol;long long calls=0,caps=0,jobs=0;int seed,rev,lo,hi,which,best=0;set<P> seen;ofstream out;mt19937 rng{921103};
 Lower(string f):out(f){}
 void emit(){int length=q.size()+head.size()+tail.size()-1;if(length<best)return;if(length>best){best=length;cout<<"new lower maximum "<<length<<endl;}if(length<goal)return;P p(head.rbegin(),head.rend());p.insert(p.end(),q.begin(),q.end());p.insert(p.end(),tail.begin(),tail.end());P key=p;key.push_back(256);key.insert(key.end(),sec.begin(),sec.end());if(!seen.insert(key).second)return;out<<seed<<" "<<rev<<" "<<lo<<" "<<hi<<" "<<p.size();for(int v:p)out<<" "<<v;out<<" "<<sec.size();for(int v:sec)out<<" "<<v;out<<endl;nsol++;}
 void dfs(bool left,int start){if(nodes++>=budget||nsol>=4)return;calls++;int n=q.size()+head.size()+tail.size()-1;emit();if(n>=goal)return;
  auto& arm=left?head:tail;int v=arm.empty()?(left?q.front():q.back()):arm.back();if(left && (head.size()==0||head.size()%(getenv("FULL_SPLIT")?1:3)==0))dfs(false,0);
  for(int d:order){int x=v^1<<d;if(occ[x]||nbr[x]!=1)continue;mark(occ,nbr,x,1);arm.push_back(x);dfs(left,0);arm.pop_back();mark(occ,nbr,x,-1);if(nodes>=budget||nsol>=4)break;}}
 void run(){occ={};nbr={};for(int v:sec)mark(occ,nbr,v,1);for(int v:q)if(occ[v]||nbr[v])return;for(int v:q)mark(occ,nbr,v,1);nodes=0;nsol=0;jobs++;dfs(true,0);caps+=nodes>=budget;}
};
int main(int argc,char**argv){if(argc!=5)return 2;Lower r(string(argv[4])+".dat");r.budget=stoi(argv[1]);int runs=stoi(argv[2]);r.goal=stoi(argv[3]);ifstream f("seeds.dat");vector<P> bases;int ix;while(f>>ix){bases.push_back(readp(f));readp(f);readp(f);}if(getenv("RSEED"))r.rng.seed(atoi(getenv("RSEED")));int total=0;for(;total<runs && r.seen.size()<1500;total++){r.seed=r.rng()%2;r.rev=r.rng()%2;P p=bases[r.seed];if(r.rev)reverse(p.begin(),p.end());int len=45+r.rng()%40,lo=r.rng()%(95-len),hi=lo+len;r.lo=lo;r.hi=hi;r.q=P(p.begin()+lo,p.begin()+hi+1);A ban{};for(int v:r.q){ban[v]=1;for(int j=0;j<8;j++)ban[v^1<<j]=1;}vector<P> shorts;
 for(int x=0;x<256;x++)if(!ban[x])for(int d=0;d<8;d++){int y=x^1<<d;if(ban[y])continue;for(int e=0;e<8;e++){int z=y^1<<e;if(e==d||ban[z])continue;for(int m=0;m<8;m++){int w=z^1<<m;if(m==e||m==d||ban[w]||w<=x)continue;shorts.push_back({x,y,z,w});}}}
 if(shorts.empty())continue;r.sec=shorts[r.rng()%shorts.size()];
  for(int j=0;j<8;j++)r.order[j]=j;shuffle(r.order.begin(),r.order.end(),r.rng);r.run();}
 cout<<"runs "<<total<<" jobs "<<r.jobs<<" calls "<<r.calls<<" caps "<<r.caps<<" compatible distinct "<<r.seen.size()<<" main_best "<<r.best<<endl;
}
