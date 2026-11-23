#define Q9_PARITY_LIBRARY
#include "../search_q9_fixed_parity.cpp"
#include <fstream>
#include <sstream>
#include <set>
#include <random>
#include <cassert>
using namespace std;using Cells=vector<int>;using Key=array<uint64_t,4>;
vector<int> masks;bool ctl;int forceL,forceR,tgt,row,groupLimit;long long nodes,upper,low,dead,unknown,total,found,skips,visited,groups,budgeted;long long per;set<Key> tested;
bool viable(Search&s,bool majority,int minimum){for(int v:s.fixed){int t=0;if(v<0)continue;for(int d=0;d<9;d++)t+=popcount(unsigned(s.axes[v^(1<<d)]))<=2;if(t<minimum)return false;}return true;}
bool forest(const Cells&m,int u){int p[9];for(int i=0;i<9;i++)p[i]=i;auto get=[&](int x){while(x!=p[x])x=p[x];return x;};for(int j=(int(m.size())/3)*3;j<m.size();j++){int e=m[j];int a=countr_zero(unsigned(e)),b=countr_zero(unsigned(e&(e-1)));p[get(a)]=get(b);}int a=countr_zero(unsigned(u)),b=countr_zero(unsigned(u&(u-1)));return get(a)!=get(b);}
bool dfs(Search&s,int two,int l,int r,int remainingL,int remainingR,Key& key,Cells &lm,Cells&rm){
 if(per>=groupLimit)return false;per++;nodes++;
 if(!remainingL&&!remainingR){visited++;if(!tested.insert(key).second){skips++;return false;}upper++;bool hit=s.test();low+=s.low;dead+=s.dead;unknown+=s.unknown;s.low=s.dead=s.unknown=0;if(hit)found++;return hit;}
 bool left=remainingL>0;int v=left?l:r;auto& map=left?lm:rm;
 for(int m:masks){if(!forest(map,m))continue;int x=v^m;if(ctl&&x!=(left?forceL:forceR))continue;if(s.slot[x]>=0)continue;int avail=0;for(int d=0;d<9;d++)avail+=popcount(unsigned(s.axes[x^(1<<d)]))<=1;if(avail<(s.majority?1:2))continue;
 int i=s.fixed.size();s.fixed.push_back(x);s.toggle(x,i,true);key[x>>7]^=1ULL<<((x>>1)&63);map.push_back(m);
 bool ok=remainingL+remainingR==1||viable(s,s.majority,s.majority?1:2);bool hit=ok&&dfs(s,two,left?x:l,left?r:x,remainingL-left,remainingR-!left,key,lm,rm);
 map.pop_back();key[x>>7]^=1ULL<<((x>>1)&63);s.toggle(x,i,false);s.fixed.pop_back();if(hit||per>=groupLimit)return hit;
 }return false;
}
int main(int argc,char**argv){assert(argc==6);ifstream f(argv[1]);tgt=stoi(argv[2]);ctl=stoi(argv[3]);int maxAdds=stoi(argv[4]);groupLimit=stoi(argv[5]);for(int i=0;i<9;i++)for(int j=0;j<i;j++)masks.push_back((1<<i)|(1<<j));
 string line;while(getline(f,line)){istringstream in(line);int n;in>>n;Cells v(n);for(int&x:v)in>>x;if(ctl)in>>forceL>>forceR;bool success=false;
 for(bool majority:{true,false}){if(ctl&&!majority)continue;int goal=tgt/2+(majority?1:0),add=goal-n;if(add<0||add>maxAdds)continue;tested.clear();
 Search s(v,50000,majority);Key k{};for(int x:v)k[x>>7]^=1ULL<<((x>>1)&63);for(int left=0;left<=add;left++){if(ctl&&left!=1)continue;groups++;per=0;Cells lm,rm;bool hit=dfs(s,0,v.front(),v.back(),left,add-left,k,lm,rm);budgeted+=per>=groupLimit;if(hit){success=true;if(!ctl){cout<<"HIT "<<row<<" "<<n<<" "<<left<<" "<<add-left<<endl;return 0;}break;}}
 }if(ctl)assert(success);row++;}cout<<"DONE rows "<<row<<" groups "<<groups<<" nodes "<<nodes<<" completed_placements "<<visited<<" tested_sets_per_row "<<upper<<" duplicate_sets "<<skips<<" low "<<low<<" hamilton_exhausted "<<dead<<" hamilton_budget "<<unknown<<" group_budget "<<budgeted<<" found "<<found<<endl;}
