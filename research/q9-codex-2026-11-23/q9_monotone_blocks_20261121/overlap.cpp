#define USE_PARTITION_CORE
#include "partition.cpp"
#undef main
struct Sub{Half8 f;int omit,translation,pi;};
struct Any:Whole{
 long long testedMaps=0,earlyFeasible=0,smallForests=0,nonparallel=0,same=0;long long keep=0;
 vector<Sub> inside(int i,int j){
 auto&A=b[i],&C=b[j];int degree[128]{},ne[256]{},am[256][8]{},sat[256]{};for(int x:A.vs)degree[x]=A.two[x]?2:A.one[x]?1:0;
 for(int x=0;x<256;x++)for(int t=0;t<8;t++){int y=x^(1<<t);if(y<128&&A.points[y]){am[x][ne[x]++]=y;sat[x]+=degree[y]==2;}}
 int cd[128]{};for(int x:C.vs)cd[x]=C.two[x]?2:C.one[x]?1:0;
 vector<Sub>out;for(int omit=0;omit<8;omit++){unsigned short expand[128];for(int v=0;v<128;v++)expand[v]=(v&((1<<omit)-1))|((v>>omit)<<(omit+1));
 for(int pi=0;pi<5040;pi++){int img[128];for(int x:C.vs)img[x]=expand[lut[pi][x]];
 for(int tx=0;tx<256;tx++){++testedMaps;bool ok=true;for(int x:C.vs){int y=img[x]^tx;if((y<128&&A.points[y])||sat[y]||cd[x]+ne[y]>2){ok=false;break;}}if(!ok)continue;++earlyFeasible;
 array<signed char,128>inc{};for(int x:C.vs){int y=img[x]^tx;for(int k=0;k<ne[y];k++){int a=am[y][k];if(degree[a]+ ++inc[a]>2){ok=false;break;}}if(!ok)break;}if(!ok)continue;
 Half8 h;h.deg.fill(-1);for(int x:A.vs){h.vs.push_back(x);h.deg[x]=degree[x]+inc[x];}for(int x:C.vs){int y=img[x]^tx;h.vs.push_back(y);h.deg[y]=cd[x]+ne[y];}
 for(int y:h.vs)if(h.deg[y]<2){h.ports.push_back(y);h.demand+=2-h.deg[y];if(!h.deg[y])h.iso.push_back(y);}
 if(h.iso.size()>2)continue;bitset<256>seen;for(int v:h.vs)if(!seen[v]){bool tip=false;vector<int>nodes{v};seen.set(v);for(int f=0;f<(int)nodes.size();f++){int x=nodes[f];tip|=h.deg[x]<2;for(int d=0;d<8;d++){int y=x^1<<d;if(!seen[y]&&h.deg[y]>=0){nodes.push_back(y);seen.set(y);}}}if(!tip){ok=false;break;}}
 if(!ok)continue;out.push_back({std::move(h),omit,tx,pi});++smallForests;nonparallel+=omit!=7;same+=omit==7&&!(tx&128);
 }}}
 return out;
 }
 bool runAny(const vector<int>&p){++sourceCuts;n=p.size();for(auto&S:b)S=Block{};
 for(int v:p){int g=(v>>x&1)+2*(v>>y&1),u=0,j=0;for(int k=0;k<9;k++)if(k!=x&&k!=y)u|=(v>>k&1)<<j++;b[g].points.set(u);b[g].vs.push_back(u);}
 for(auto&S:b)for(int v:S.vs){int h=0;for(int k=0;k<7;k++)h+=S.points[v^(1<<k)];if(h>2){internal++;return false;}(h==0?S.zero:h==1?S.one:S.two).set(v);}
 for(int j=1;j<4;j++){int c=j==1?2:1,d=6-c-j;auto l=inside(0,j),r=inside(c,d);
 for(auto&u:l)for(auto&v:r)if(combine(u.f,v.f,0,j,c,d,{u.pi,u.translation},{v.pi,v.translation})){cout<<"SUPPORT "<<id<<' '<<x<<' '<<y<<' '<<u.omit<<' '<<v.omit<<endl;return true;}}
 return false;
 }
};
int main(int argc,char**argv){if(argc!=3)return 2;array<int,7>p;iota(p.begin(),p.end(),0);do{int k=pr.size();pr.push_back(p);pid[code(p)]=k;for(int v=1;v<128;v++)lut[k][v]=lut[k][v&(v-1)]^(1<<p[countr_zero((unsigned)v)]);}while(next_permutation(p.begin(),p.end()));
 array<int,8>q;iota(q.begin(),q.end(),0);do{int k=perm8.size();perm8.push_back(q);for(int v=1;v<256;v++)l8[k][v]=l8[k][v&(v-1)]^(1<<q[countr_zero((unsigned)v)]);}while(next_permutation(q.begin(),q.end()));
 Any s;ifstream f(argv[1]);string line;int maxrows=stoi(argv[2]);while(s.sourceCuts<maxrows&&getline(f,line)){istringstream is(line);is>>s.id>>s.x>>s.y;int v;vector<int>p;while(is>>v)p.push_back(v);if(s.runAny(p)&&p.size()>=193)break;}
 cout<<"DONE cases "<<s.sourceCuts<<" rejected_internal "<<s.internal<<" relative_maps "<<s.testedMaps<<" passed_first_filter "<<s.earlyFeasible<<" forests "<<s.smallForests<<" nonparallel_forests "<<s.nonparallel<<" coincident_face_forests "<<s.same<<" forest_pairs "<<s.pairs<<" feasible_port_counts "<<s.filtered<<" eight_dimensional_placements "<<s.candidates<<" valid_degrees "<<s.validDegrees<<" disconnected "<<s.disconnected<<" hits "<<s.succeeded<<endl;
}
