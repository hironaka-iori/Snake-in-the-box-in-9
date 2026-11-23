#define main check_main
#include "replay.cpp"
#undef main
#include <numeric>
#include <random>
struct St{array<unsigned char,24> z{};int value=0,colour=0,e=0;};
struct Vtx{int v=-1;vector<St>st;int part[24]{},pos[24]{};};
struct Face{vector<St>st;};
struct Use{int v,k;};
int main(int argc,char**argv){
 if(argc!=5)return 2;read_mothers(argv[1]);init();int sweeps=stoi(argv[2]),threshold=stoi(argv[3]),scale=10000;vector<int>dir;
 for(char const *p=argv[4];*p;){char*e;dir.push_back(strtol(p,&e,10));p=(*e==',')?e+1:e;}int K=dir.size();assert(K<=24);mt19937 gen(872913);
 int i,x;while(cin>>i>>x){Cert cert;cert.scale=scale;cert.balance=0;cert.fees[0]=cert.fees[1]=0;cert.axes.resize(K);
 for(int k=0;k<K;k++){auto&a=cert.axes[k];a.mask=dir[k];int d[3],t=0;for(int j=0;j<8;j++)if(a.mask>>j&1)d[t++]=j;assert(t==3);
  for(int z=0;z<8;z++)for(int j=0;j<3;j++)if(z>>j&1)a.expand[z]|=1<<d[j];for(int s=0;s<256;s++)for(int j=0;j<3;j++)a.compress[s]|=((s>>d[j])&1)<<j;}
 Layout shape(i,x);auto &low=shape.low,&port=shape.port,&pool=shape.pool;
 int m=shape.m,delta=shape.delta,nlow=shape.nlow;
 gen.seed(872913+65537*i+991*x);
 vector<Vtx>vtx(256);vector<Face>faces;vector<Use>uses;
 vector<array<unsigned char,256>>avail(K);
 for(int v=0;v<256;v++)if(pool[v]){
  auto &q=vtx[v];q.v=v;int allowed=0;for(int d=0;d<8;d++)if(pool[v^(1<<d)])allowed|=1<<d;
  int sg=1-2*(popcount(unsigned(v))%2);
  for(int s=allowed;;s=(s-1)&allowed){int deg=popcount(unsigned(s))+port[v];if(deg==2||(deg==1&&shape.upper_ends&&popcount(unsigned(v))%2!=m)){
   St z;z.value=scale;z.colour=sg;z.e=deg==1;for(int k=0;k<K;k++){z.z[k]=cert.axes[k].compress[s];avail[k][v]|=1<<z.z[k];}q.st.push_back(z);}if(!s)break;}
  if(!port[v]){St z;z.z.fill(8);q.st.push_back(z);}
 }
 for(int k=0;k<K;k++){auto&a=cert.axes[k];for(int b=0;b<256;b++)if(!(b&a.mask)){int ff=faces.size();faces.emplace_back();int ban=0,force=0;
  for(int j=0;j<8;j++){int v=b^a.expand[j];if(!pool[v])ban|=1<<j;if(port[v])force|=1<<j;if(pool[v]){vtx[v].part[k]=ff;vtx[v].pos[k]=j;uses.push_back({v,k});}}
  for(auto &pat:patterns)if(!(pat.on&ban)&&(pat.on&force)==force){St z;z.z.fill(8);bool ok=true;
   for(int on=pat.on;on;on&=on-1){int j=countr_zero(unsigned(on));int v=b^a.expand[j];z.z[j]=pat.sig[j];if(!((avail[k][v]>>z.z[j])&1)){ok=false;break;}}
   if(ok)faces[ff].st.push_back(z);}
 }}
 bool empty=false;for(auto &q:vtx)if(q.v>=0&&q.st.empty())empty=true;for(auto&g:faces)empty|=g.st.empty();
 if(empty){assert(score(i,x,cert)==-1000000000000LL);cout<<"R "<<i<<" "<<x<<" -1000000000000 10000 0 0 0 0\nE"<<endl;continue;}
 const int neg=-1000000000;auto optimize=[&](){
  array<int,256>A0,B0;A0.fill(neg);B0.fill(neg);
  for(auto&q:vtx)if(q.v>=0)for(auto&t:q.st)if(t.colour){int raw=t.value+t.colour*cert.balance+t.e*cert.fees[m];auto &best=(t.e?B0:A0)[q.v];best=max(best,raw);}
  auto cost=[&](int bal){int fee=neg;array<int,256>a,b;
   for(auto&q:vtx)if(q.v>=0){int v=q.v,sg=1-2*(popcount(unsigned(v))%2);a[v]=A0[v]-sg*bal;if(!port[v])a[v]=max(0,a[v]);b[v]=B0[v]-sg*bal;if(B0[v]>neg/2&&a[v]>neg/2)fee=max(fee,b[v]-a[v]);}
   if(fee==neg)fee=0;int total=shape.upper_ends*fee+bal*delta;for(auto&q:vtx)if(q.v>=0)total+=max(a[q.v],b[q.v]-fee);return pair<int,int>{total,fee};};
  int l=-scale*15,r=scale*15;while(l<r){int j=l+(r-l)/2;if(cost(j).first<=cost(j+1).first)r=j;else l=j+1;}
  auto [sum,fee]=cost(l);for(auto&q:vtx)if(q.v>=0)for(auto&t:q.st)t.value+=(cert.balance-l)*t.colour+(cert.fees[m]-fee)*t.e;
  cert.balance=l;cert.fees[m]=fee;
 };
 LL val=0;int used=0;
 for(int sw=0;sw<=sweeps;sw++){
  optimize();val=LL(nlow)*scale+delta*cert.balance+shape.upper_ends*cert.fees[m];
  for(auto&q:vtx)if(q.v>=0)val+=max_element(q.st.begin(),q.st.end(),[](auto&a,auto&b){return a.value<b.value;})->value;
  for(auto&q:faces)val+=max_element(q.st.begin(),q.st.end(),[](auto&a,auto&b){return a.value<b.value;})->value;
  used=sw;if(val<LL(scale)*threshold||sw==sweeps)break;
  shuffle(uses.begin(),uses.end(),gen);
  for(auto [v,k]:uses){auto&q=vtx[v];auto&g=faces[q.part[k]];int pos=q.pos[k];int a[9],b[9],step[9]{};fill(a,a+9,neg);fill(b,b+9,neg);
   for(auto&t:q.st)a[t.z[k]]=max(a[t.z[k]],t.value);
   for(auto&t:g.st)b[t.z[pos]]=max(b[t.z[pos]],t.value);
   int ref=8;if(a[ref]==neg||b[ref]==neg){int best=neg;for(int j=0;j<9;j++)if(a[j]!=neg&&b[j]!=neg&&a[j]+b[j]>best){best=a[j]+b[j];ref=j;}if(best==neg)continue;}
   int ar=a[ref],br=b[ref];for(int j=0;j<8;j++){
    if(a[j]!=neg&&b[j]!=neg)step[j]=((b[j]-br)-(a[j]-ar))/2;
    else if(a[j]!=neg)step[j]=min(0,ar-a[j]-scale);else if(b[j]!=neg)step[j]=max(0,b[j]-br+scale);
    cert.axes[k].price[v][j]+=step[j];
   }
   for(auto&t:q.st)t.value+=step[t.z[k]];
   for(auto&t:g.st)t.value-=step[t.z[pos]];
  }
 }
 assert(score(i,x,cert)==val);
 cout<<"R "<<i<<" "<<x<<" "<<val<<" "<<scale<<" "<<cert.balance<<" "<<cert.fees[0]<<" "<<cert.fees[1]<<" "<<used<<"\n";
 for(auto&a:cert.axes)for(int v=0;v<256;v++)for(int z=0;z<8;z++)if(a.price[v][z])cout<<a.mask<<" "<<v<<" "<<a.expand[z]<<" "<<a.price[v][z]<<"\n";
 cout<<"E"<<endl;
 }}
