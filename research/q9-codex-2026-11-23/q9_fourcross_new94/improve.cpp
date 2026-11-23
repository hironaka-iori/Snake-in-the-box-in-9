#define main old_main
#include "search.cpp"
#undef main
struct Improve{
 A u{},ns{};P p,s,r;int a,b,goal,nodes,budget,id,seed,rev,lo,hi;long long calls=0,caps=0,jobs=0;set<P> seen;ofstream out;array<int,8> dirs{0,1,2,3,4,5,6,7};mt19937 rng{90526};
 Improve(string n):out(n){}
 void walk(int len){if(++nodes>budget)return;calls++;int v=r.back(),t=p[b];if(popcount((unsigned)(t^v))>len)return;
 if(len==1){if(!near(v,t)||ns[t]!=(1+(b+1<(int)p.size())))return;P q(p.begin(),p.begin()+a);q.insert(q.end(),r.begin(),r.end());q.insert(q.end(),p.begin()+b,p.end());P key=q;key.push_back(256);key.insert(key.end(),s.begin(),s.end());if(!seen.insert(key).second)return;
 out<<seed<<" "<<rev<<" "<<lo<<" "<<hi<<" "<<q.size();for(int x:q)out<<" "<<x;out<<" "<<s.size();for(int x:s)out<<" "<<x;out<<endl;return;}
 for(int d:dirs){int x=v^1<<d;if(x==t||u[x]||ns[x]!=1)continue;mark(u,ns,x,1);r.push_back(x);walk(len-1);r.pop_back();mark(u,ns,x,-1);if(nodes>budget)break;}}
 void solve(){u={};ns={};for(int x:s)mark(u,ns,x,1);for(int i=0;i<=a;i++)mark(u,ns,p[i],1);for(int i=b+1;i<(int)p.size();i++)mark(u,ns,p[i],1);r={p[a]};nodes=0;jobs++;walk(b-a+goal-((int)p.size()-1));caps+=nodes>budget;}
};
int main(int argc,char**v){if(argc!=6)return 2;Improve z(v[5]);z.goal=atoi(v[2]);z.budget=atoi(v[3]);int maxwin=atoi(v[4]);ifstream in(v[1]);while(in>>z.seed>>z.rev>>z.lo>>z.hi){z.p=readp(in);z.s=readp(in);for(int w=2;w<=maxwin;w++)for(z.a=0;z.a+w<(int)z.p.size();z.a++){z.b=z.a+w;shuffle(z.dirs.begin(),z.dirs.end(),z.rng);z.solve();}if(z.seen.size()>2000)break;}
 cout<<"jobs "<<z.jobs<<" calls "<<z.calls<<" caps "<<z.caps<<" positive "<<z.seen.size()<<endl;}
