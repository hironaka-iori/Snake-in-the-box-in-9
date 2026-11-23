#define main root_check_cli
#include "replay.cpp"
#undef main
struct Group{vector<int> scope;vector<pair<int,int>> opts;};
int main(int argc,char**argv){
 assert(argc==4);ifstream bank(argv[1]);string w;while(bank>>w)words.push_back(w);init();
 int i=stoi(argv[2]),x=stoi(argv[3]),m=popcount(unsigned(x))%2;
 Cert c;char cmd;int id,K,nw;cin>>cmd>>id>>c.scale>>c.fees[0]>>c.fees[1]>>c.balance>>K>>nw;assert(cmd=='C'&&id==0);map<int,int>idx;c.axes.resize(K);
 for(int k=0;k<K;k++){auto&a=c.axes[k];cin>>a.mask;idx[a.mask]=k;int count=0,d[3];for(int j=0;j<8;j++)if(a.mask>>j&1)d[count++]=j;assert(count==3);
  for(int z=0;z<8;z++)for(int j=0;j<3;j++)if(z>>j&1)a.expand[z]|=1<<d[j];
  for(int s=0;s<256;s++)for(int j=0;j<3;j++)a.compress[s]|=((s>>d[j])&1)<<j;}
 for(int k=0;k<nw;k++){int g,v,s,p;cin>>g>>v>>s>>p;auto&a=c.axes[idx.at(g)];assert(a.expand[a.compress[s]]==s);a.price[v][a.compress[s]]=p;}assert(cin);
 array<bool,256>low{},port{},pool{};int cur=0;low[0]=true;for(char d:words[i]){cur^=1<<(d-'0');low[cur]=true;}low[x]=port[x]=port[cur]=port[0]=true;
 int nlow=0,npool=0,delta=-(1-2*m);for(int v=0;v<256;v++){pool[v]=!low[v]||port[v];npool+=pool[v];nlow+=low[v];if(low[v])delta+=1-2*(popcount(unsigned(v))%2);}
 int base=nlow*c.scale+delta*c.balance+c.fees[m];vector<Group> groups;
 vector<array<int,256>>supported(K);
 for(int v=0;v<256;v++)if(pool[v]){Group g;g.scope={v};vector<int>dirs;
  for(int d=0;d<8;d++)if(pool[v^(1<<d)])g.scope.push_back(v^(1<<d));sort(g.scope.begin()+1,g.scope.end());
  const int p=popcount(unsigned(v))%2;
  for(int b=0;b<1<<(g.scope.size()-1);b++){if(!port[v])g.opts.push_back({2*b,0});int deg=popcount(unsigned(b))+port[v];if(deg!=2&&!(deg==1&&p!=m))continue;
   int mask=0;for(int j=1;j<g.scope.size();j++)if(b>>(j-1)&1)mask|=(v^g.scope[j]);int val=c.scale-(1-2*p)*c.balance-(deg==1?c.fees[m]:0);
   for(int k=0;k<K;k++){auto&a=c.axes[k];int z=a.compress[mask];supported[k][v]|=1<<z;val+=a.price[v][z];}g.opts.push_back({2*b+1,val});}
  assert(!g.opts.empty());groups.push_back(move(g));}
 for(int k=0;k<K;k++){auto&a=c.axes[k];for(int b=0;b<256;b++)if(!(b&a.mask)){
  Group g;int ban=0,req=0;array<int,8>compact{};for(int j=0;j<8;j++){int v=b^a.expand[j];if(!pool[v])ban|=1<<j;else{compact[j]=g.scope.size();g.scope.push_back(v);}if(port[v])req|=1<<j;}
  if(g.scope.empty())continue;
  for(auto&p:patterns){if((p.on&ban)||(p.on&req)!=req)continue;int val=0,bits=0;bool ok=true;
   for(int t=p.on;t;t&=t-1){int j=countr_zero(unsigned(t)),v=b^a.expand[j],z=p.sig[j];if(!(supported[k][v]>>z&1)){ok=false;break;}
    val-=a.price[v][z];bits|=1<<compact[j];}if(ok)g.opts.push_back({bits,val});}
  assert(!g.opts.empty());groups.push_back(move(g));}}
 LL total=base;for(auto&g:groups){int best=-100000000;for(auto [z,val]:g.opts)best=max(best,val);total+=best;}assert(total==score(i,x,c));
 cout<<base<<" "<<c.scale<<" "<<total<<" "<<groups.size()<<" "<<npool<<" "<<nlow<<" "<<m<<"\n";
 for(int v=0;v<256;v++)if(pool[v])cout<<v+256<<" ";cout<<"\n";for(int v=0;v<256;v++)if(low[v])cout<<v<<" ";cout<<"\n";
 for(auto&g:groups){cout<<g.scope.size()<<" "<<g.opts.size();for(int v:g.scope)cout<<" "<<v+256;cout<<"\n";for(auto [z,val]:g.opts)cout<<z<<" "<<val<<"\n";}
}
