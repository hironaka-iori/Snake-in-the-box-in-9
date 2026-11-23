#define Q9_PARITY_LIBRARY
#include "../search_q9_fixed_parity.cpp"
#include <fstream>
#include <sstream>
#include <cassert>
using P=vector<int>;using U=uint64_t;
struct Perm{array<array<uint16_t,8>,3> t;};vector<Perm> group;
void permutations(){array<int,9>d{0,1,2,3,4,5,6,7,8};do{Perm p{};for(int i=0;i<3;i++)for(int b=1;b<8;b++)p.t[i][b]=p.t[i][b&(b-1)]|(1<<d[3*i+countr_zero(unsigned(b))]);group.push_back(p);}while(next_permutation(d.begin(),d.end()));assert(group.size()==362880);}
int applyP(const Perm&p,int v){return p.t[0][v&7]|p.t[1][(v>>3)&7]|p.t[2][v>>6];}
P anchors(const P&m){P v{0};for(int x:m)v.push_back(v.back()^x);return v;}
bool induced(const P&p){for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||(popcount(unsigned(p[i]^p[j]))==1)!=(j+1==i))return false;return true;}
U tried=0,nodisjoint=0,disjoint=0,original=0,ham=0,unknown=0,completions=0,cheap=0,loDeg=0;bool wasControl=false;
bool side(const P&v,const array<unsigned short,512>&load,const array<int,512>&loc,P&path){
 Graph g(v,50000);array<unsigned,50> opts{};for(int odd=1;odd<512;odd++){unsigned m=load[odd];if(popcount(m)!=2)continue;int x=odd^(m&-m);m&=m-1;int y=odd^m;int a=loc[x],b=loc[y];if(a<0||b<0)continue;g.add(a,b,odd);}
 int tips=0;for(int j=0;j<v.size();j++){int deg=g.adj[j].size();if(deg==0||((j>0)&&deg==1&&++tips>1)){loDeg++;return false;}}
 int forced=g.edges.size();for(int j=0;j<v.size();j++)g.add(j,g.dummy,-1);vector<int8_t> state(g.edges.size());state[forced]=1;ham++;int ret=g.visit(state);if(ret<0){unknown++;return false;}if(!ret)return false;path=g.witness;if(path.front()!=0)reverse(path.begin(),path.end());assert(path.front()==0&&path.size()==2*v.size()-1&&induced(path));return true;}
int ordered(const P&v,const array<unsigned short,512>&load){for(int j=1;j<v.size();j++){unsigned m=v[j]^v[j-1];int o=v[j-1]^(m&-m),p=v[j]^ (m&-m);if(popcount(unsigned(load[o]))!=2&&popcount(unsigned(load[p]))!=2)return 0;}return 1;}
bool run(const P&A,const P&B,int row){auto a=anchors(A),b=anchors(B);array<bool,512> used{};array<int,512> al;al.fill(-1);array<unsigned short,512> base{};for(int j=0;j<a.size();j++){used[a[j]]=true;al[a[j]]=j;for(int k=1;k<512;k*=2)base[a[j]^k]|=k;}
 for(int pi=0;pi<group.size();pi++){const auto&p=group[pi];tried++;bool ok=true;P v(b.size());for(int j=1;j<b.size();j++){int x=applyP(p,b[j]);if(used[x]){ok=false;break;}v[j]=x;}if(!ok){nodisjoint++;continue;}disjoint++;auto load=base;array<int,512>bl;bl.fill(-1);bl[0]=0;for(int j=1;j<v.size();j++){int x=v[j];bl[x]=j;for(int k=1;k<512;k*=2)load[x^k]|=k;}
 int orderedPair=ordered(a,load)&&ordered(v,load);original+=orderedPair;P left,right;if(!side(a,load,al,left)||!side(v,load,bl,right)){assert(!orderedPair);continue;}
 reverse(left.begin(),left.end());left.insert(left.end(),right.begin()+1,right.end());assert(induced(left));completions++;
 cout<<"JOIN "<<row<<" "<<pi<<" "<<orderedPair<<" "<<left.size()-1;for(auto x:left)cout<<" "<<x;cout<<endl;return true;
 }return false;}
int main(int argc,char**argv){ifstream f(argv[1]);string l;permutations();int row=0;while(getline(f,l)){istringstream in(l);int n,m;in>>n>>m;P a(n),b(m);for(int&x:a)in>>x;for(int&x:b)in>>x;bool hit=run(a,b,row);if(stoi(argv[2]))assert(hit);else if(hit)break;row++;if(row%100==0)cout<<"AT "<<row<<" "<<tried<<" "<<disjoint<<endl;}
 cout<<"DONE rows "<<row<<" permutations "<<tried<<" intersect "<<nodisjoint<<" disjoint "<<disjoint<<" ordered "<<original<<" hamilton "<<ham<<" low "<<loDeg<<" unknown "<<unknown<<" hits "<<completions<<endl;}
