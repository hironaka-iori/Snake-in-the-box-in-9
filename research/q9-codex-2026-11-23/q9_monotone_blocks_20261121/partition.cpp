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
 long long pairs=0,filtered=0,plans=0,candidates=0,late=0,validDegrees=0,disconnected=0,succeeded=0,sourceCuts=0;
 bool combine(const Half8&L,const Half8&R,int a,int b,int c,int d,Map lm,Map rm){
 ++pairs;if(!L.usable||!R.usable)return false;int sum=L.demand+R.demand-2;if(sum%2)return false;int m=sum/2,eL=L.demand-m,eR=R.demand-m;
 if(m<=0||eL<0||eR<0||m>min(L.ports.size(),R.ports.size())||eL<(int)L.iso.size()||eR<(int)R.iso.size())return false;++filtered;
 int missL=L.ports.size()-m,missR=R.ports.size()-m;vector<int>anch=L.iso;if(anch.empty())anch=L.ports;anch.resize(L.iso.empty()?missL+1:1);
 for(int pi=0;pi<40320;pi++){const auto &img=l8[pi];++plans;bitset<256>tried;for(int u:anch)for(int v:R.ports){int t=u^img[v];if(tried[t])continue;tried.set(t);++candidates;
 int missed=0;bool ok=true;for(int x:R.ports){int deg=L.deg[img[x]^t];if(deg>=2){ok=false;break;}if(deg<0&&(R.deg[x]==0||++missed>missR)){ok=false;break;}}
 if(!ok||missed!=missR)continue;++late;bitset<256>right;for(int x:R.vs){int pos=img[x]^t;right.set(pos);if(R.deg[x]==2&&L.deg[pos]>=0){ok=false;break;}}if(!ok)continue;for(int x:L.iso)if(!right[x]){ok=false;break;}if(!ok)continue;
 ++validDegrees;bitset<512>sel;for(int x:L.vs)sel[x]=1;for(int x:R.vs)sel[256+(img[x]^t)]=1;
 int start=-1,tips=0;for(int x=0;x<512;x++)if(sel[x]){int k=0;for(int j=0;j<9;j++)k+=sel[x^(1<<j)];assert(k==1||k==2);if(k==1){start=x;tips++;}}assert(tips==2);
 vector<int>p{start};int prev=-1;while(true){int x=p.back(),u=-1;for(int j=0;j<9;j++)if(sel[x^(1<<j)]&&(x^(1<<j))!=prev){u=x^(1<<j);break;}if(u<0)break;prev=x;p.push_back(u);}
 if(p.size()!=sel.count()){++disconnected;continue;}++succeeded;
 cout<<"HIT "<<id<<' '<<this->x<<' '<<this->y<<' '<<a<<b<<c<<d<<' '<<lm.p<<' '<<lm.t<<' '<<rm.p<<' '<<rm.t<<' '<<pi<<' '<<t;for(int x:p)cout<<' '<<x;cout<<endl;return true;
 }}return false;
 }
 bool run(const vector<int>&p){++sourceCuts;n=p.size();for(int k=0;k<4;k++){b[k]=Block{};for(int j=0;j<4;j++)edge[k][j].clear();}
 for(int v:p){int g=(v>>x&1)+2*(v>>y&1),u=0,j=0;for(int k=0;k<9;k++)if(k!=x&&k!=y)u|=(v>>k&1)<<j++;b[g].points.set(u);b[g].vs.push_back(u);}
 for(auto&S:b)for(int v:S.vs){int h=0;for(int k=0;k<7;k++)h+=S.points[v^(1<<k)];if(h>2){internal++;return false;}(h==0?S.zero:h==1?S.one:S.two).set(v);}
 for(int j=1;j<4;j++){int c=j==1?2:1,d=6-c-j;build(0,j);build(c,d);vector<Half8>lhs,rhs;for(auto&e:edge[0][j])lhs.push_back(forest(b[0],b[j],e.m));for(auto&e:edge[c][d])rhs.push_back(forest(b[c],b[d],e.m));
 for(int i=0;i<(int)lhs.size();i++)for(int k=0;k<(int)rhs.size();k++)if(combine(lhs[i],rhs[k],0,j,c,d,edge[0][j][i].m,edge[c][d][k].m))return true;}
 return false;}
};
#ifndef USE_PARTITION_CORE
int main(int argc,char**argv){if(argc!=3)return 2;array<int,7>p;iota(p.begin(),p.end(),0);do{int k=pr.size();pr.push_back(p);pid[code(p)]=k;for(int v=1;v<128;v++)lut[k][v]=lut[k][v&(v-1)]^(1<<p[countr_zero((unsigned)v)]);}while(next_permutation(p.begin(),p.end()));
 array<int,8>q;iota(q.begin(),q.end(),0);do{int k=perm8.size();perm8.push_back(q);for(int v=1;v<256;v++)l8[k][v]=l8[k][v&(v-1)]^(1<<q[countr_zero((unsigned)v)]);}while(next_permutation(q.begin(),q.end()));
 Whole s;ifstream f(argv[1]);string line;int maxrows=stoi(argv[2]);while(s.sourceCuts<maxrows&&getline(f,line)){istringstream is(line);is>>s.id>>s.x>>s.y;int v;vector<int>seq;while(is>>v)seq.push_back(v);if(s.run(seq)&&seq.size()>=193)break;}
 cout<<"DONE cases "<<s.sourceCuts<<" degree_impossible "<<s.internal<<" pair_isometries "<<s.mapChecks<<" retained_pairs "<<s.pairOK<<" forest_pairs "<<s.pairs<<" feasible_port_counts "<<s.filtered<<" eight_axis_permutations "<<s.plans<<" eight_dimensional_placements "<<s.candidates<<" passed_right_ports "<<s.late<<" degree_compatible "<<s.validDegrees<<" disconnected "<<s.disconnected<<" hits "<<s.succeeded<<endl;}

#endif
