#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
using P=vector<int>;using Pair=array<P,2>;using Mask=array<uint64_t,4>;
unsigned char deg[256],on[256],orig[256];int nb[256][8],target,maxDel,minDel,sec,maxAdd,best,recordMin;long long cases,nodes,solutions,completions;bool stopped=false;
chrono::steady_clock::time_point start;P outer,live;set<Mask> seen;
void setv(int x,int sign){on[x]=sign>0;for(int y:nb[x])deg[y]+=sign;}
void emit(){++completions;Pair a;bool visited[256]{};int idx=0;
 for(int x=0;x<256;x++)if(on[x]&&deg[x]<=1&&!visited[x]){
   if(idx>=2)return;
   int now=x,prev=-1;while(now>=0){if(visited[now])return;visited[now]=true;a[idx].push_back(now);int z=-1;for(int y:nb[now])if(on[y]&&y!=prev)z=y;prev=now;now=z;}idx++;
 }
 if(idx!=2||a[0].size()+a[1].size()!=target)return;
 Mask m{};for(auto&p:a)for(int x:p)m[x/64]|=1ull<<(x%64);if(!seen.insert(m).second)return;
 ++solutions;if(solutions>30000&&target<=100)return;int off=a[0][0];for(auto&p:a){cout<<p.size();for(int x:p)cout<<" "<<(x^off);cout<<" ";}cout<<endl;best=max(best,target);}
bool legal(int x){if(deg[x]>2)return false;for(int y:nb[x])if(on[y]&&deg[y]>=2)return false;return true;}
void adds(P const& ev,int i,int k,int e){++nodes;if(e<0||e>2*k||ev.size()-i<k)return;if(!k){if(!e)emit();return;}for(;i+k<=ev.size();i++){int x=ev[i],d=deg[x];if(d>e||!legal(x))continue;setv(x,1);adds(ev,i+1,k-1,e-d);setv(x,-1);}}
void del(int i,int k,int n,int e){
 if(k){for(;i+k<=live.size()&&!stopped;i++){int x=live[i],d=deg[x];setv(x,-1);del(i+1,k-1,n-1,e-d);setv(x,1);}return;}
 ++cases;
 if((cases&16383)==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>=sec){stopped=true;return;}
 int add=target-n,edge=target-2-e;if(edge<0||edge>2*add)return;
 // With k additions, every final addition consumes at most two incident edges.
 P ev;for(int x:outer)if(legal(x))ev.push_back(x);
 if(ev.size()>=add)adds(ev,0,add,edge);
}
int main(int argc,char**argv){if(argc!=7)return 1;target=atoi(argv[1]);minDel=atoi(argv[2]);maxDel=atoi(argv[3]);maxAdd=atoi(argv[4]);recordMin=atoi(argv[5]);sec=atoi(argv[6]);for(int x=0;x<256;x++)for(int d=0;d<8;d++)nb[x][d]=x^(1<<d);start=chrono::steady_clock::now();vector<vector<P>> seeds;string s;
 while(getline(cin,s)){istringstream in(s);int n,v;vector<P> p;while(in>>n){P w;while(n--){in>>v;w.push_back(v);}p.push_back(w);}int total=0;for(auto&w:p)total+=w.size();if(total>=recordMin)seeds.push_back(p);}
 for(int k=minDel;k<=maxDel&&!stopped;k++){for(auto&p:seeds){int total=0;for(auto&w:p)total+=w.size();if(target-total+k<0||target-total+k>maxAdd)continue;
 live.clear();outer.clear();for(auto&w:p)for(int x:w){setv(x,1);live.push_back(x);}for(int x=0;x<256;x++)if(!on[x])outer.push_back(x);
 del(0,k,total,total-p.size());for(int x:live)setv(x,-1);if(stopped)break;}}
 cerr<<"target "<<target<<" donors "<<seeds.size()<<" deletions "<<cases<<" nodes "<<nodes<<" edge_matched "<<completions<<" solutions "<<solutions<<" max "<<best<<" cutoff "<<stopped<<endl;
}
