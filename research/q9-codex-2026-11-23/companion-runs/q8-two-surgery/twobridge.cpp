#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <sstream>
#include <vector>
using namespace std;using P=vector<int>;using Pair=array<P,2>;using M=__uint128_t;
int wt(M m){return popcount(uint64_t(m))+popcount(uint64_t(m>>64));}
struct Half{P nodes;M mask=0,sat=0;int edges=0,ports=0;};
Half project(P const& vs,int axis,int side){Half h;for(int v:vs)if((v>>axis&1)==side){int y=(v&((1<<axis)-1))|(v>>(axis+1)<<axis);h.nodes.push_back(y);h.mask|=M(1)<<y;}
 for(int y:h.nodes){int d=0;for(int j=0;j<7;j++)d+=(h.mask>>(y^(1<<j)))&1;h.edges+=d;if(d==2)h.sat|=M(1)<<y;else h.ports++;}h.edges/=2;return h;}
M maskOn[7];M xs(M s,int x){for(int j=0;j<7;j++)if(x>>j&1)s=((s&maskOn[j])>>(1<<j))|((s&~maskOn[j])<<(1<<j));return s;}
long long placements=0,repairs=0,uniqueDone=0,finished=0,proposed=0;int best=0;
using Occupied=array<uint64_t,4>;set<Occupied> seen,sols;int nb[256][8],degree[256],target,sourceCap,repairCap;bool on[256],orig[256];
void mark(int x,int sign){for(int y:nb[x])degree[y]+=sign;on[x]=sign>0;}
void check(){++finished;int count=0;Pair arms;bool used[256]{};int cc=0;
 for(int x=0;x<256;x++)if(on[x]){count++;if(used[x]||degree[x]>1)continue;if(cc==2)return;
 int y=x,prev=-1;while(y!=-1){if(used[y])return;used[y]=true;arms[cc].push_back(y);int z=-1;for(int v:nb[y])if(on[v]&&v!=prev){if(z>=0)return;z=v;}prev=y;y=z;}cc++;}
 if(cc!=2||arms[0].size()+arms[1].size()!=count)return;Occupied m{};for(auto&p:arms)for(int x:p)m[x/64]|=1ull<<(x%64);
 if(!sols.insert(m).second)return;int zero=arms[0][0];for(auto&p:arms){cout<<p.size();for(int v:p)cout<<" "<<(v^zero);cout<<" ";}cout<<endl;best=max(best,count);++proposed;
}
void add(P&opts,int first,int rem,int edgeNeed){
 if(rem==0){if(!edgeNeed)check();return;}if(edgeNeed<0||edgeNeed>2*rem)return;
 for(int i=first;i+rem<=opts.size();i++){int v=opts[i];if(degree[v]>2)continue;bool ok=true;for(int y:nb[v])if(on[y]&&degree[y]>=2)ok=false;if(!ok)continue;int d=degree[v];mark(v,1);add(opts,i+1,rem-1,edgeNeed-d);mark(v,-1);}
}
void deletion(P&bad,int n,int e,int rest){
 int v=-1;for(int x:bad)if(on[x]&&degree[x]>2){v=x;break;}
 if(v<0){int diff=target-n;if(diff<0||diff>repairCap+2)return;P opts;
 for(int x=0;x<256;x++)if(!orig[x] && degree[x]<=2){bool ok=true;for(int y:nb[x])if(on[y]&&degree[y]>=2)ok=false;if(ok)opts.push_back(x);}
 if(opts.size()>=diff)add(opts,0,diff,target-2-e);return;}
 if(!rest)return;P branch{v};for(int y:nb[v])if(on[y])branch.push_back(y);
 for(int x:branch){int d=degree[x];mark(x,-1);deletion(bad,n-1,e-d,rest-1);mark(x,1);}
}
void repair(M a,M b,M defects,int n,int e){if(!defects)return;Occupied m{uint64_t(a),uint64_t(a>>64),uint64_t(b),uint64_t(b>>64)};
 if(!seen.insert(m).second)return;++uniqueDone;P bad;fill(on,on+256,false);fill(orig,orig+256,false);fill(degree,degree+256,0);
 for(int x=0;x<256;x++)if((m[x/64]>>(x%64))&1){orig[x]=true;mark(x,1);}
 for(int x=0;x<256;x++)if(on[x]&&degree[x]>2)bad.push_back(x);
 deletion(bad,n,e,repairCap);
}
int main(int argc,char**argv){if(argc!=7)return 2;target=stoi(argv[1]);sourceCap=stoi(argv[2]);int stride=stoi(argv[3]),offset=stoi(argv[4]);repairCap=stoi(argv[5]);int limit=stoi(argv[6]);
 for(int x=0;x<256;x++)for(int j=0;j<8;j++)nb[x][j]=x^(1<<j);
 for(int j=0;j<7;j++)for(int v=0;v<128;v++)if(v>>j&1)maskOn[j]|=M(1)<<v;
 vector<Half> hs;set<M> distinct;string line;while(getline(cin,line)){istringstream in(line);int n;P v;while(in>>n){int x;for(int j=0;j<n;j++){in>>x;v.push_back(x);}}
 for(int i=0;i<8;i++)for(int side:{0,1}){auto h=project(v,i,side);if(distinct.insert(h.mask).second)hs.push_back(h);}if(hs.size()>=sourceCap)break;}
 if(hs.size()>sourceCap)hs.resize(sourceCap);sort(hs.begin(),hs.end(),[](auto&a,auto&b){return a.nodes.size()>b.nodes.size();});
 array<int,7> pi{0,1,2,3,4,5,6};int k=0;do{if(k++%stride!=offset)continue;int map[128]{};for(int x=1;x<128;x++)map[x]=map[x&(x-1)]|1<<countr_zero(unsigned(1<<pi[countr_zero(unsigned(x))]));
 for(int j=0;j<hs.size();j++){auto &b=hs[j];M bm=0,bs=0;for(int x:b.nodes){bm|=M(1)<<map[x];if((b.sat>>x)&1)bs|=M(1)<<map[x];}
 for(int t=0;t<128;t++){M mm=xs(bm,t),sat=xs(bs,t);for(int i=0;i<=j;i++){auto&a=hs[i];int n=a.nodes.size()+b.nodes.size();if(n<target-2)break;if(n>target+repairCap)continue;
 ++placements;M overlap=mm&a.mask,defect=(mm&a.sat)|(sat&a.mask);int d=wt(defect);
 if(d<1||d>repairCap || wt(overlap)>12)continue;int e=a.edges+b.edges+wt(overlap);if(e-3*repairCap>target-2||e+2*(target-n+repairCap)<target-2)continue;
 ++repairs;repair(a.mask,mm,defect,n,e);if(uniqueDone>=limit)goto Done;
 }}}
 }while(next_permutation(pi.begin(),pi.end()));
 Done:cerr<<"slices "<<hs.size()<<" placements "<<placements<<" admitted "<<repairs<<" unique_done "<<uniqueDone<<" terminal_graphs "<<finished<<" saved "<<proposed<<" best "<<best<<endl;
}
