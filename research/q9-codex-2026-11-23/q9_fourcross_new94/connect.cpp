#define main old_main
#include "search.cpp"
#undef main
struct F{int seed,rev,lo,hi,id;P q,s;};
struct Connect{
 F f;P mid,a,b,q,s;A used{},nb{},forb{};long long joins=0,ccalls=0,acalls=0,caps=0;int best=0,goal=192,checks=0,budget,local,jlim,jnodes=0,maxjoins=120;array<int,8> order,armord;mt19937 rng{1861121};ofstream out;
 Connect(string nm):out(nm){}
 void emit(){int length=(int)q.size()+s.size()+mid.size()+a.size()+b.size()-1;if(length<=best)return;P x;for(auto it=a.rbegin();it!=a.rend();it++)x.push_back(256+*it);x.insert(x.end(),q.begin(),q.end());for(int v:mid)x.push_back(v+256);x.insert(x.end(),s.begin(),s.end());for(int v:b)x.push_back(v+256);
 for(int j=0;j<(int)x.size();j++)for(int i=0;i<j;i++)if(x[i]==x[j]||near(x[i],x[j])!=(j==i+1))abort();best=length;out<<length<<" "<<f.id<<" "<<f.seed<<" "<<q.size()-1<<" "<<s.size()-1;for(int v:x)out<<" "<<v;out<<endl;if(length>=192)cout<<"FOUND "<<length<<endl;
 }
 void arms(bool left){if(best>=goal||++local>budget)return;acalls++;emit();if(left&&(a.size()+b.size())%2==0)arms(false);P&z=left?a:b;int v=z.back();for(int d:armord){int x=v^1<<d;if(used[x]||nb[x]!=1||forb[x])continue;mark(used,nb,x,1);z.push_back(x);arms(left);z.pop_back();mark(used,nb,x,-1);if(local>budget||best>=goal)break;}}
 void bridge(int rem){if(++jnodes>jlim||checks>=maxjoins||best>=goal)return;ccalls++;int v=mid.back(),end=s[0];if(popcount((unsigned)(v^end))>rem)return;
 if(!rem){if(v!=end)return;joins++;checks++;local=0;shuffle(armord.begin(),armord.end(),rng);arms(true);caps+=local>budget;return;}
 for(int d:order){int x=v^1<<d;if((x==end)!=(rem==1)||used[x]||nb[x]!=1||(forb[x]&&x!=end))continue;mark(used,nb,x,1);mid.push_back(x);bridge(rem-1);mid.pop_back();mark(used,nb,x,-1);if(jnodes>jlim||checks>=maxjoins||best>=goal)break;}}
 void run(int code,int extra){q=f.q;s=f.s;if(code&1)reverse(q.begin(),q.end());if(code&2)reverse(s.begin(),s.end());if(code&4)swap(q,s);
  used={};nb={};forb={};for(int x:q)forb[x]=1;for(int x:s)forb[x]=1;a={q[0]};b={s.back()};mid={q.back()};for(int x:{a[0],b[0],mid[0]})mark(used,nb,x,1);
  if(nb[a[0]]||nb[b[0]]||nb[mid[0]]||nb[s[0]])return;checks=0;jnodes=0;shuffle(order.begin(),order.end(),rng);int len=popcount((unsigned)(q.back()^s[0]))+2*extra;bridge(len);
 }
};
int main(int argc,char**argv){if(argc!=7)return 1;Connect c(string(argv[6])+".paths");c.budget=stoi(argv[2]);c.jlim=stoi(argv[3]);c.maxjoins=stoi(argv[4]);int rounds=stoi(argv[5]);for(int j=0;j<8;j++)c.order[j]=c.armord[j]=j;ifstream in(argv[1]);vector<F> v;int o,r,l,h;while(in>>o>>r>>l>>h){F f{o,r,l,h,int(v.size()),readp(in),readp(in)};v.push_back(f);}for(int t=0;t<rounds;t++){shuffle(v.begin(),v.end(),c.rng);for(auto&f:v){c.f=f;for(int j=0;j<8;j++){c.run(j,(t+j)%11);if(c.best>=192)goto done;}}}done:cout<<"forests "<<v.size()<<" joins "<<c.joins<<" bridgecalls "<<c.ccalls<<" armcalls "<<c.acalls<<" armlimit "<<c.caps<<" best "<<c.best<<endl;}
