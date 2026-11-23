#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <vector>
#include <iostream>
#include <fstream>
#include <set>
#include <cassert>
using namespace std;
using B=uint64_t;
B bit(int x){return B(1)<<x;}
int sz(B b){return popcount(b);}
int low(B b){return countr_zero(b);}
int sw(int v,int t){for(int j=0;j<2*t;j+=2)if(((v>>j)^(v>>(j+1)))&1)v^=3<<j;return v;}
int parity(int x){return popcount((unsigned)x)%2;}
bool pathok(const vector<int>&p){for(int j=1;j<(int)p.size();j++)for(int i=0;i<j;i++)if(p[i]==p[j]||((popcount((unsigned)(p[i]^p[j]))==1)!=(i+1==j)))return false;return true;}
struct Wing{
 int h,n=0,id[128],rep[64],best=0;B adj[64]{},root=0,sides=0,all;
 vector<int> stack,record;
 Wing(int t):h(t-1){
 fill(id,id+128,-1);
 for(int i=0;i<128;i++)if(i<sw(i,h)){rep[n]=i;id[i]=id[sw(i,h)]=n;if(!parity(i))sides|=bit(n);if(popcount((unsigned)i)==1)root|=bit(n);n++;}
 all=bit(n)-1;
 for(int i=0;i<n;i++)for(int j=0;j<7;j++){int q=id[rep[i]^(1<<j)];if(q>=0)adj[i]|=bit(q);}
 }
 B reach(int x,B allowed){B frontier=bit(x),seen=frontier;while(frontier){B next=0;for(B v=frontier;v;v&=v-1)next|=adj[low(v)];frontier=next&allowed&~seen;seen|=frontier;}return seen;}
 int bound(int x,B allowed){B v=reach(x,allowed);int a=sz(v&sides),b=sz(v&~sides);return min(a+b,2*min(a,b)+1);}
 void dfs(int x,B allowed,bool needroot){stack.push_back(x);bool at=root&bit(x);
 if((!needroot||at)&&(int)stack.size()>best){best=stack.size();record=stack;}
 if(!needroot||!at){B nxt=adj[x]&allowed, remain=allowed&~adj[x]&~bit(x);
 for(B z=nxt;z;z&=z-1){int y=low(z);B r=reach(y,remain|bit(y));if(needroot&&!(r&root))continue;
 int a=sz(r&sides),b=sz(r&~sides);if((int)stack.size()+min(a+b,2*min(a,b)+1)>best)dfs(y,remain,needroot);}}
 stack.pop_back();}
 vector<int> solve(int x,B allowed,bool needroot){best=0;record.clear();dfs(x,allowed,needroot);return record;}
};
int main(int argc,char**argv){int t=atoi(argv[1]);Wing w(t); ifstream fin(argv[2]);int cap=atoi(argv[3]),best=0,bestupper=0,nrows=0,m;
 long long tested=0,legal=0,demand=0,exact=0;array<int,7> p={0,1,2,3,4,5,6};vector<array<int,128>> maps;
 do{bool good=true;for(int i=0;i<t-1;i++){if(p[2*i]>p[2*i+1]||(i&&p[2*i-2]>p[2*i]))good=false;}
 for(int i=2*(t-1)+1;i<7;i++)if(p[i-1]>p[i])good=false;
 if(good){array<int,128> a{};for(int x=0;x<128;x++)for(int j=0;j<7;j++)a[x]|=((x>>p[j])&1)<<j;maps.push_back(a);}
 }while(next_permutation(p.begin(),p.end()));
 cerr<<"t "<<t<<" maps "<<maps.size()<<" wing "<<w.n<<endl;
 while(nrows<cap&&fin>>m){nrows++;vector<int> donor(m);for(int &i:donor)fin>>i;assert(pathok(donor));
 for(auto &a:maps)for(int shift=0;shift<128;shift++){tested++;vector<int> mid;B used=0;int freq[64]{};bool touches=false;
 for(int v:donor){int x=a[v]^shift;mid.push_back(x);if(!x)touches=true;if(w.id[x]>=0){freq[w.id[x]]++;used|=bit(w.id[x]);}}
 if(touches)continue;int first=w.id[mid.front()],last=w.id[mid.back()];if(first<0||last<0||freq[first]!=1||freq[last]!=1)continue;
 for(int orient=0;orient<2;orient++,swap(first,last),reverse(mid.begin(),mid.end())){B free=w.all^used;B incoming=free|bit(first),outgoing=free|bit(last);
 B c=w.reach(first,incoming);if(!(c&w.root))continue;legal++;int upper=m+w.bound(first,incoming)+w.bound(last,outgoing);bestupper=max(bestupper,upper);demand+=upper>=96;
 if(upper<=best)continue;auto in=w.solve(first,incoming,true);if(in.empty()||m+(int)in.size()+w.bound(last,outgoing)<=best)continue;
 auto out=w.solve(last,outgoing,false);exact++;int found=m+in.size()+out.size();if(found<=best)continue;
 vector<int> orbit;for(auto it=in.rbegin();it!=in.rend();it++)orbit.push_back(w.rep[*it]<<2);for(int x:mid)orbit.push_back(1+(x<<2));for(int j:out)orbit.push_back(3+(w.rep[j]<<2));
 vector<int> arm={0};for(int v:orbit){if(popcount((unsigned)(arm.back()^v))!=1)v=sw(v,t);assert(popcount((unsigned)(arm.back()^v))==1);arm.push_back(v);}
 vector<int> witness;for(int j=arm.size()-1;j>0;j--)witness.push_back(sw(arm[j],t));witness.insert(witness.end(),arm.begin(),arm.end());assert(pathok(witness));
 best=found;cout<<"record "<<2*best<<" row "<<nrows<<" lengths "<<in.size()<<' '<<m<<' '<<out.size()<<" vertices";for(int v:witness)cout<<' '<<v;cout<<endl;
 }}
 }
 cerr<<"donors "<<nrows<<" placements "<<tested<<" legal_oriented "<<legal<<" bound_ge96 "<<demand<<" max_coarse_upper "<<bestupper<<" exact_out_calls "<<exact<<" best "<<2*best<<endl;
}
