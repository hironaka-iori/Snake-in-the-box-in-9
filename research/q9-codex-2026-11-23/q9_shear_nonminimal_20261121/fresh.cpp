#define main source_partial_main
#include "../search_q9_sheared_geodesics.cpp"
#undef main
struct Tip{int v,len;};
vector<Tip> tips(int root,int diff,const array<int,512>& touch,const array<int,512>& occupied){
 vector<Tip> out{{root,0}};
 for(int m=(diff-1)&diff;m;m=(m-1)&diff){
  int x=root^m,h=popcount(unsigned(m));if(!occupied[x]&&touch[x]==int(h==1))out.push_back({x,h});
 }return out;
}

#include <fstream>
#include <functional>
#include <map>
struct Result{bool ok;int stage;};
Result reduce(const vector<int>& anchors,const array<int,512>& touch,const array<int,512>& occ){
 vector<vector<int>> ranks;
 for(int i=1;i<anchors.size();++i){
  int u=anchors[i-1],v=anchors[i],m=u^v,h=popcount(unsigned(m));if(h==1)continue;
  array<unsigned char,512> ok{},forward{},back{};
  ok[0]=ok[m]=forward[0]=back[m]=1;
  for(int x=(m-1)&m;x;x=(x-1)&m){
   int y=u^x;
   ok[x]=!occ[y]&&touch[y]==int(has_single_bit(unsigned(x)))+int(has_single_bit(unsigned(m^x)));
  }
  for(int x=(-m)&m;x;x=(x-m)&m){
   if(ok[x])for(int q=x;q;q&=q-1)if(forward[x^(q&-q)]){forward[x]=1;break;}
   if(x==m)break;
  }
  if(!forward[m])return {false,1};
  int o=ranks.size();ranks.resize(o+h-1);
  for(int x=(m-1)&m;x;x=(x-1)&m){
   if(!forward[x])continue;
   for(int q=m^x;q;q&=q-1)if(back[x^(q&-q)]){back[x]=1;break;}
   if(back[x])ranks[o+popcount(unsigned(x))-1].push_back(u^x);
  }
 }
 vector<int> ids(ranks.size());iota(ids.begin(),ids.end(),0);sort(ids.begin(),ids.end(),[&](int a,int b){return ranks[a].size()<ranks[b].size();});
 array<int,512> slot,visited{};slot.fill(-1);int stamp=0;
 function<bool(int)> aug=[&](int i){
  for(int y:ranks[i]){if(visited[y]==stamp)continue;visited[y]=stamp;
   if(slot[y]<0||aug(slot[y])){slot[y]=i;return true;}}
  return false;
 };
 for(int i:ids){++stamp;if(!aug(i))return {false,2};}
 return {true,0};
}
int main(int argc,char**argv){
 if(argc!=7&&argc!=8)return 2;bool integral=argc==8;int goal=stoi(argv[1]),first=stoi(argv[2]),last=stoi(argv[3]),lo=stoi(argv[4]),hi=stoi(argv[5]);ofstream pending(argv[6]);
 string w;int row=-1;
 while(cin>>w){
 ++row;if(row<first||row>last)continue;
 vector<int> orig{0};for(char c:w)orig.push_back(orig.back()^(1<<(c-'0')));int n=orig.size();
 long long maps=0,windows=0,trials=0,dp=0,hall=0,exported=0,rt=0;
 for(int d=0;d<9;d++)for(int t=1;t<512;t++){
  int h=popcount(unsigned(t));if((t&(1<<d))||h<lo||h>hi)continue;maps++;
  vector<int>v(n),cost(n);for(int i=0;i<n;++i){v[i]=orig[i]^(((orig[i]>>d)&1)?t:0);if(i)cost[i]=cost[i-1]+popcount(unsigned(v[i]^v[i-1]));}
  array<int,512> when;when.fill(-1);int s=0;
  for(int j=0;j<n;++j){
   int x=v[j];s=max(s,when[x]+1);
   for(int bit=0;bit<9;++bit){int k=when[x^(1<<bit)];if(k!=j-1)s=max(s,k+1);}
   when[x]=j;int right=j+1<n?v[j]^v[j+1]:0,rmax=max(0,popcount(unsigned(right))-1);
   for(int a=s;a<j;++a){
    int remain=goal-(cost[j]-cost[a]);if(integral){if(remain<0)continue;if(remain>0)break;}else{if(remain<=0)continue;if(remain>h+rmax)break;}
    int left=a?v[a]^v[a-1]:0,lmax=max(0,popcount(unsigned(left))-1);if(remain>lmax+rmax)continue;
    ++windows;array<int,512>touch{},occ{};vector<int> core(v.begin()+a,v.begin()+j+1);
    for(int y:core){occ[y]=1;for(int b=0;b<9;++b)++touch[y^(1<<b)];}
    auto A=tips(v[a],left,touch,occ),B=tips(v[j],right,touch,occ);
    int np=0;for(auto l:A)for(auto r:B)if(l.len+r.len==remain&&l.v!=r.v&&!has_single_bit(unsigned(l.v^r.v)))++np;
    trials+=np;if(!np)continue;
    vector<int> blocked,stretched;
    for(int ix=0;ix+1<core.size();++ix){
     if(popcount(unsigned(core[ix]^core[ix+1]))==1)continue;
     stretched.push_back(ix);
     if(!reduce({core[ix],core[ix+1]},touch,occ).ok)blocked.push_back(ix);
     if(blocked.size()>2)break;
    }
    if(blocked.size()>2 || stretched.empty())continue;
    ++exported;rt+=np;
    pending<<row<<" "<<d<<" "<<t<<" "<<a<<" "<<j<<" "<<left<<" "<<right<<" "<<remain<<" "<<np<<" "<<blocked.size();
    for(int v:blocked)pending<<" "<<v;
    for(int v:core)pending<<" "<<v;pending<<"\n";
   }
  }
 }
 cout<<row<<" "<<maps<<" "<<windows<<" "<<trials<<" "<<dp<<" "<<hall<<" "<<exported<<" "<<rt<<endl;pending.flush();
 }
}
