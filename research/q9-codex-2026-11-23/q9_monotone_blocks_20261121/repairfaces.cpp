#define main parallel_driver
#include "faces.cpp"
#undef main
array<array<unsigned char,256>,40320>l8;vector<array<int,8>>perm8;
struct Half8{array<signed char,256>deg;vector<int>vs,ports,iso;int demand=0;bool usable=true;};
Half8 forest(const Block&A,const Block&B,Map m){
 Half8 h;h.deg.fill(-1);for(int x:A.vs){h.vs.push_back(x);h.deg[x]=0;}for(int x:B.vs){int u=128+m.at(x);h.vs.push_back(u);h.deg[u]=0;}
 for(int v:h.vs){int d=0;for(int k=0;k<8;k++)d+=h.deg[v^(1<<k)]>=0;h.deg[v]=d;assert(d<=2);h.demand+=2-d;if(d<2)h.ports.push_back(v);if(!d)h.iso.push_back(v);}
 bitset<256> seen;for(int v:h.vs)if(!seen[v]){vector<int>nodes{v};seen[v]=true;bool tip=false;for(int j=0;j<(int)nodes.size();j++){int u=nodes[j];tip|=h.deg[u]<2;for(int k=0;k<8;k++){int w=u^(1<<k);if(h.deg[w]>=0&&!seen[w]){seen.set(w);nodes.push_back(w);}}}if(!tip)h.usable=false;}
 return h;
}
struct Whole:Fit{
 int holes=1,retired=0;long long filltries=0;
 bool fill(bitset<512> ss,int remain,vector<int>&p,vector<int>&inserted){
    ++filltries;array<int,512> deg{};int ep=0,root=-1;bitset<512>opts;
    for(int v=0;v<512;v++)if(ss[v]){for(int k=0;k<9;k++)deg[v]+=ss[v^(1<<k)];if(deg[v]>2)return false;ep+=2-deg[v];if(deg[v]==1)root=v;if(deg[v]<2)for(int k=0;k<9;k++)opts.set(v^(1<<k));}
    if(ep>2+2*remain||ep<2)return false;
    if(!remain){if(ep!=2||root<0)return false;p={root};int prev=-1;while(true){int dest=-1;for(int k=0;k<9;k++){int t=p.back()^(1<<k);if(t!=prev&&ss[t]){dest=t;break;}}if(dest<0)break;prev=p.back();p.push_back(dest);}return p.size()==ss.count();}
    opts&=~ss;for(int v=0;v<512;v++)if(opts[v]){int nn=0;bool ok=true;for(int k=0;k<9;k++){int u=v^(1<<k);if(ss[u]){nn++;if(deg[u]>=2)ok=false;}}if(!ok||nn>2||nn<1)continue;ss.set(v);inserted.push_back(v);if(fill(ss,remain-1,p,inserted))return true;inserted.pop_back();ss.reset(v);}return false;
 }
 void buildLoose(int a,int c){auto&A=b[a],&C=b[c];for(int k=0;k<5040;k++){const auto&f=lut[k];for(int t=0;t<128;t++){++mapChecks;Mask ma,mc;bool ok=true;for(int v:C.vs){int u=f[v]^t;if(!A.points[u])continue;if(A.two[u]||C.two[v]){ok=false;break;}ma.set(u);mc.set(v);}if(!ok||(A.zero&~ma).count()+(C.zero&~mc).count()>2+2*holes)continue;Map chart{k,t};edge[a][c].push_back({chart,ma,mc});++pairOK;}}}

 long long pairs=0,filtered=0,plans=0,candidates=0,late=0,validDegrees=0,disconnected=0,succeeded=0,sourceCuts=0;
 bool combine(const Half8&L,const Half8&R,int a,int b,int c,int d,Map lm,Map rm){
 ++pairs;if(!L.usable||!R.usable)return false;for(int deficit=2;deficit<=2+2*holes;deficit+=2){int sum=L.demand+R.demand-deficit;if(sum%2)continue;int m=sum/2,eL=L.demand-m,eR=R.demand-m;
 if(m<0||eL<0||eR<0||m>min(L.ports.size(),R.ports.size())||eL<(int)L.iso.size()||eR<(int)R.iso.size())continue;++filtered;
 int missL=L.ports.size()-m,missR=R.ports.size()-m;vector<int>anch=L.ports;if(m)anch.resize(missL+1);
 for(int pi=0;pi<40320;pi++){const auto &img=l8[pi];++plans;bitset<256>tried;if(!m)tried.set();else for(int u:anch)for(int v:R.ports)tried.set(u^img[v]);for(int t=0;t<256;t++)if(tried[t]){++candidates;
 int missed=0;bool ok=true;for(int x:R.ports){int deg=L.deg[img[x]^t];if(deg>=2){ok=false;break;}if(deg<0&&++missed>missR){ok=false;break;}}
 if(!ok||missed!=missR)continue;++late;bitset<256>right;for(int x:R.vs){int pos=img[x]^t;right.set(pos);if(R.deg[x]==2&&L.deg[pos]>=0){ok=false;break;}}if(!ok)continue;
 ++validDegrees;bitset<512>sel;for(int x:L.vs)sel[x]=1;for(int x:R.vs)sel[256+(img[x]^t)]=1;
 vector<int>p,inserted;if(!fill(sel,holes,p,inserted)){++disconnected;continue;}++succeeded;
 cout<<"HIT "<<id<<' '<<this->x<<' '<<this->y<<' '<<a<<b<<c<<d<<' '<<lm.p<<' '<<lm.t<<' '<<rm.p<<' '<<rm.t<<' '<<pi<<' '<<t<<' '<<holes;for(int q:inserted)cout<<' '<<q;for(int x:p)cout<<' '<<x;cout<<endl;return true;
 }}}return false;
 }
 bool run(const vector<int>&p){++sourceCuts;n=p.size();for(int k=0;k<4;k++){b[k]=Block{};for(int j=0;j<4;j++)edge[k][j].clear();}
 for(int v:p){int g=(v>>x&1)+2*(v>>y&1),u=0,j=0;for(int k=0;k<9;k++)if(k!=x&&k!=y)u|=(v>>k&1)<<j++;b[g].points.set(u);b[g].vs.push_back(u);}
 for(auto&S:b)for(int v:S.vs){int h=0;for(int k=0;k<7;k++)h+=S.points[v^(1<<k)];if(h>2){internal++;return false;}(h==0?S.zero:h==1?S.one:S.two).set(v);}
 for(int j=1;j<4;j++){int c=j==1?2:1,d=6-c-j;buildLoose(0,j);buildLoose(c,d);vector<Half8>lhs,rhs;for(auto&e:edge[0][j])lhs.push_back(forest(b[0],b[j],e.m));for(auto&e:edge[c][d])rhs.push_back(forest(b[c],b[d],e.m));
 for(int i=0;i<(int)lhs.size();i++)for(int k=0;k<(int)rhs.size();k++)if(combine(lhs[i],rhs[k],0,j,c,d,edge[0][j][i].m,edge[c][d][k].m))return true;}
 return false;}
};
int main(int argc,char**argv){if(argc!=4)return 2;array<int,7>p;iota(p.begin(),p.end(),0);do{int k=pr.size();pr.push_back(p);pid[code(p)]=k;for(int v=1;v<128;v++)lut[k][v]=lut[k][v&(v-1)]^(1<<p[countr_zero((unsigned)v)]);}while(next_permutation(p.begin(),p.end()));
 array<int,8>q;iota(q.begin(),q.end(),0);do{int k=perm8.size();perm8.push_back(q);for(int v=1;v<256;v++)l8[k][v]=l8[k][v&(v-1)]^(1<<q[countr_zero((unsigned)v)]);}while(next_permutation(q.begin(),q.end()));
 Whole s;s.holes=stoi(argv[3]);ifstream f(argv[1]);string line;int maxrows=stoi(argv[2]);while(s.sourceCuts<maxrows&&getline(f,line)){istringstream is(line);is>>s.id>>s.x>>s.y;int v;vector<int>seq;while(is>>v)seq.push_back(v);if(s.run(seq)&&seq.size()+s.holes>=193)break;}
 cout<<"DONE cases "<<s.sourceCuts<<" degree_impossible "<<s.internal<<" pair_isometries "<<s.mapChecks<<" retained_pairs "<<s.pairOK<<" forest_pairs "<<s.pairs<<" feasible_port_counts "<<s.filtered<<" eight_axis_permutations "<<s.plans<<" eight_dimensional_placements "<<s.candidates<<" passed_right_ports "<<s.late<<" degree_compatible "<<s.validDegrees<<" disconnected "<<s.disconnected<<" fill_nodes "<<s.filltries<<" hits "<<s.succeeded<<endl;}
