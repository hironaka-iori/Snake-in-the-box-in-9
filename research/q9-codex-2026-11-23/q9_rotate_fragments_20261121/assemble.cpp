#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
unsigned seed=19218779;unsigned rd(){seed^=seed<<13;seed^=seed>>17;return seed^=seed<<5;}
int h(int x,int y){return popcount(unsigned(x^y));}
vector<vector<int>>bank,frags;vector<int>path,order;array<int,512>occ,deg,links,port,dist;int mode,goal,maxadd,budget,coreSize,edges,seenBest,caseid,inputid,usedMask,allMask;
long long nodes,joins,attempts,complete,changedOrder,positive,limited,trialNodes,caseHits;set<vector<int>>witnesses;
void toggle(int v,int delta){occ[v]+=delta;for(int d=0;d<9;d++){int w=v^(1<<d);deg[w]+=delta;links[w]^=v;}}
void verify(const vector<int>&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)assert(p[i]!=p[j]&&((h(p[i],p[j])==1)==(i==j+1)));}
vector<int> normalize(vector<int>p){array<int,9>m;m.fill(-1);int n=0;vector<int>w;for(int j=1;j<p.size();j++){int axis=countr_zero(unsigned(p[j]^p[j-1]));if(m[axis]<0)m[axis]=n++;w.push_back(m[axis]);}return w;}
void record(){
 complete++;caseHits++;int n=path.size()-1;if(n<189)return;
 auto ids=order;bool asc=is_sorted(ids.begin(),ids.end()),desc=is_sorted(ids.rbegin(),ids.rend());if(!asc&&!desc)changedOrder++;
 bool better=n>seenBest;seenBest=max(seenBest,n);if(n<190||(!better&&witnesses.size()>800&&n<192))return;
 auto w=normalize(path);auto q=path;reverse(q.begin(),q.end());w=min(w,normalize(q));if(!witnesses.insert(w).second)return;
 verify(path);cout<<"W "<<n<<" "<<inputid<<" "<<caseid<<" "<<coreSize<<" "<<frags.size()<<" "<<!asc*!desc;for(int v:path)cout<<" "<<v;cout<<endl;
}
int lower(int tip,int un){int nearest=10;for(unsigned u=un;u;u&=u-1){int i=countr_zero(u);nearest=min(nearest,min(h(tip,frags[i].front()),h(tip,frags[i].back())));}return nearest-1+max(0,popcount(unsigned(un))-1);}
void dfs(int add,bool flipped){
 if(trialNodes>=budget||seenBest>=goal)return;nodes++;trialNodes++;int un=usedMask^allMask;if(!un){record();if(seenBest>=goal)return;
 if(!flipped){reverse(path.begin(),path.end());dfs(add,true);reverse(path.begin(),path.end());}}
 if(add==maxadd)return;int v=path.back();if(un&&add+lower(v,un)>maxadd)return;
 int ys[9],prior[9],n=0;for(int d=0;d<9;d++){int y=v^(1<<d);if(occ[y]||deg[y]>2)continue;
  int through=-1;if(deg[y]==2){int x=links[y]^v;through=port[x];if(through<0||((usedMask>>through)&1))continue;}
  ys[n]=y;prior[n++]=(through>=0?0:1)+(un&&through<0?lower(y,un):0);}
 for(int i=0;i<n;i++){int best=i;for(int z=i+1;z<n;z++)if(prior[z]<prior[best]||(prior[z]==prior[best]&&rd()%2))best=z;swap(ys[i],ys[best]);swap(prior[i],prior[best]);}
 for(int j=0;j<n&&trialNodes<budget&&seenBest<goal;j++){int y=ys[j],other=deg[y]==2?links[y]^v:-1;int a=other<0?-1:port[other];toggle(y,1);path.push_back(y);
 if(a>=0){joins++;usedMask^=1<<a;order.push_back(a);auto &z=frags[a];bool rev=other!=z.front();if(rev)path.insert(path.end(),z.rbegin(),z.rend());else path.insert(path.end(),z.begin(),z.end());dfs(add+1,flipped);path.resize(path.size()-z.size());order.pop_back();usedMask^=1<<a;}else dfs(add+1,flipped);
 path.pop_back();toggle(y,-1);}
}
bool source(int idx,int iter,bool ctl){
 auto &p=bank[idx];int n=p.size();vector<int>bad(n);vector<pair<int,int>>conf;
 for(int i=1;i<n;i++)if(h(p[i],p[i-1])!=1)conf.emplace_back(i,i-1);
 for(int i=0;i<n;i++)for(int j=0;j<i-1;j++)if(h(p[i],p[j])<=1)conf.emplace_back(i,j);
 auto remove=[&](int mid,int l,int r){for(int i=max(0,mid-l);i<min(n,mid+r+1);i++)bad[i]=1;};
 if(mode==3){assert(conf.size()==1);int variant=iter/int(bank.size());int source=variant%2?conf[0].first:conf[0].second;int width=(variant/2)%8;int outer=variant/16;static const int lt[]={0,1,0,1,2,3,5,8},rt[]={0,0,1,1,2,3,5,8};remove(source,lt[width],rt[width]);
 if(outer>0){int j=(outer-1)%25;int radius=(outer-1)/25+1;int v=j*8;remove(v,radius,radius);}
 }else{
 for(int j=int(conf.size())-1;j>0;j--)swap(conf[j],conf[rd()%(j+1)]);
 for(auto [a,b]:conf)if(!bad[a]&&!bad[b]){int v=rd()&1?a:b;unsigned width=rd()%100;int m=width<45?0:width<80?3:8;remove(v,rd()%(m+1),rd()%(m+1));}
 int extra=ctl?2+rd()%3:rd()%5;for(int z=0;z<extra;z++){int c=rd()%n;int w=ctl?1:1+rd()%9;remove(c,rd()%w,rd()%w);}
 if(!ctl&&rd()%4==0){int w=1+rd()%19;if(rd()%2)remove(0,0,w);else remove(n-1,w,0);}
 }
 frags.clear();coreSize=0;for(int j=0;j<n;){if(bad[j]){j++;continue;}int lo=j++;while(j<n&&!bad[j])j++;
  if(mode!=3&&!ctl&&j-lo<=int(rd()%4))continue;frags.emplace_back(p.begin()+lo,p.begin()+j);coreSize+=j-lo;}
 if(coreSize<140||frags.empty()||frags.size()>12||coreSize>=goal+1)return false;
 if(mode==4){if(frags.size()<2)return false;bool moved=false;
 vector<int>choices;for(int i=0;i<frags.size();i++)if(frags[i].size()>=5&&frags[i].size()<=80)choices.push_back(i);if(choices.empty())return false;
 for(int tr=0;tr<min(4,int(choices.size())+1)&&!moved;tr++){int i=choices[rd()%choices.size()];auto base=frags[i];array<bool,512>forbid{},inbase{};for(int v:base)inbase[v]=true;for(int j=0;j<frags.size();j++)if(j!=i)for(int x:frags[j]){forbid[x]=true;for(int k=0;k<9;k++)forbid[x^(1<<k)]=true;}
 int best=99999;vector<int>chosen;for(int z=0;z<160;z++){int n=rd()%3;int d=rd()%9,e=rd()%9,root=rd()%2?base.front():base.back();int shift=n==0?0:1<<(rd()%9);if(n==2)shift^=1<<(rd()%9);
 vector<int>q;int fresh=0;for(int v:base){int u=v^root;int a=(u>>d)&1,b=(u>>e)&1;if(a!=b)u^=(1<<d)|(1<<e);int y=u^root^shift;if(forbid[y])break;q.push_back(y);fresh+=!inbase[y];}if(q.size()!=base.size()||!fresh)continue;
 int s0=10,s1=10;for(int j=0;j<frags.size();j++)if(j!=i){for(int a:{frags[j].front(),frags[j].back()}){s0=min(s0,h(q.front(),a));s1=min(s1,h(q.back(),a));}}int score=2*(s0+s1)+rd()%11;if(score<best){best=score;chosen=move(q);}}
 if(!chosen.empty()){frags[i]=move(chosen);moved=true;}}
 if(!moved)return false;}
 if(mode==2){for(int j=frags.size()-1;j>0;j--)swap(frags[j],frags[rd()%(j+1)]);for(auto&z:frags)if(rd()&1)reverse(z.begin(),z.end());}
 occ.fill(0);deg.fill(0);links.fill(0);port.fill(-1);for(int i=0;i<frags.size();i++){for(int v:frags[i]){assert(!occ[v]);toggle(v,1);}port[frags[i].front()]=port[frags[i].back()]=i;}
 for(auto&z:frags)for(int i=0;i<z.size();i++)assert(deg[z[i]]==int(i>0)+int(i+1<z.size()));
 return true;
}
int main(int argc,char**argv){assert(argc==7);ifstream f(argv[1]);string s;while(getline(f,s)){istringstream is(s);vector<int>z;int v;while(is>>v)z.push_back(v);assert(z.size()==192||z.size()==193);bank.push_back(z);}
 int rounds=stoi(argv[2]);budget=stoi(argv[3]);goal=stoi(argv[4]);mode=stoi(argv[5]);bool ctl=mode==1||mode==2;seed=stoul(argv[6]);vector<int>ids;for(int i=0;i<bank.size();i++)ids.push_back(i);
 for(int it=0;it<rounds;it++){inputid=it%bank.size();caseid=it;if(!source(inputid,it,ctl))continue;attempts++;allMask=(1<<frags.size())-1;maxadd=goal+1-coreSize+(ctl?0:3);trialNodes=caseHits=0;if(ctl)seenBest=0;
 vector<int>starts;for(int j=0;j<frags.size()*2;j++)starts.push_back(j);for(int j=starts.size()-1;j>0;j--)swap(starts[j],starts[rd()%(j+1)]);
 for(int v:starts){if(trialNodes>=budget||seenBest>=goal)break;int k=v/2;path=frags[k];if(v%2)reverse(path.begin(),path.end());usedMask=1<<k;order={k};dfs(0,false);}if(trialNodes>=budget)limited++;if(seenBest>=goal){positive++;if(!ctl)break;}}
 cout<<"DONE attempts "<<attempts<<" nodes "<<nodes<<" joined "<<joins<<" completions "<<complete<<" reordered_189plus "<<changedOrder<<" cut "<<limited<<" targets "<<positive<<" best "<<seenBest<<" saved "<<witnesses.size()<<endl;
}
