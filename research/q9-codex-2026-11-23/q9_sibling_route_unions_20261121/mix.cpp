#include <algorithm>
#include <array>
#include <bitset>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;using Mask=bitset<512>;
struct Alt{int cost,lo,hi,repair;string w;vector<int>a,b;Mask plus,minus;array<signed char,512> adj{};};
struct Source{int id;string w;Mask mask;vector<Alt>alts;};
long long pairs=0,dis=0,within=0,one=0,simple=0,full=0;ofstream out;
string snake(const Mask& s){int first=-1,ends=0;for(int i=0;i<512;i++)if(s[i]){
 int n=0;for(int j=0;j<9;j++)n+=s[i^(1<<j)];if(n==1){if(first<0)first=i;ends++;}else if(n!=2)return "";
 }if(ends!=2)return "";int prev=-1,v=first;string w;while(true){int nxt=-1,k=0;for(int j=0;j<9;j++)if((v^(1<<j))!=prev&&s[v^(1<<j)]){nxt=v^(1<<j);k=j;break;}if(nxt<0)break;w+=char('0'+k);prev=v;v=nxt;}return w.size()+1==s.count()?w:"";}
int main(int argc,char**argv){if(argc!=4)return 2;ifstream seed(argv[1]),in(argv[2]);out.open(argv[3]);map<int,Source> all;int id,u,v,q,t;string w;
 while(seed>>id>>u>>v>>q>>t>>w){Source s{id,w};int cur=0;s.mask[cur]=1;for(char c:w){cur^=1<<(c-'0');s.mask[cur]=1;}all.emplace(id,move(s));}
 string row;while(getline(in,row)){istringstream ss(row);Alt h;int r,k;string mp;ss>>id>>h.cost>>h.repair>>h.lo>>h.hi>>r>>mp>>k;auto &s=all.at(id);h.w=s.w.substr(h.lo,h.hi-h.lo);for(char&c:h.w)c=mp[c-'0'];if(r)reverse(h.w.begin(),h.w.end());
 for(int i=0;i<k;i++){int x;ss>>x;h.a.push_back(x);h.plus[x]=1;for(int j=0;j<9;j++)h.adj[x^(1<<j)]++;}
 for(int i=0;i<k;i++){int x;ss>>x;h.b.push_back(x);h.minus[x]=1;for(int j=0;j<9;j++)h.adj[x^(1<<j)]--;}
 s.alts.push_back(move(h));}
 for(auto &[id,s]:all){int saved=0;for(int j=0;j<(int)s.alts.size();j++)for(int i=0;i<j;i++){
 auto &a=s.alts[i],&b=s.alts[j];++pairs;if((a.plus&b.plus).any()||(a.minus&b.minus).any())continue;++dis;int cost=a.cost+b.cost-2;
 for(int v:b.a)cost+=a.adj[v];for(int v:b.b)cost-=a.adj[v];if(cost>2)continue;++within;Mask ss=(s.mask^a.minus^b.minus)|a.plus|b.plus;assert(ss.count()==s.mask.count());
 if(cost<=0){string path=snake(ss);if(!path.empty()){out<<"FOUND "<<id<<' '<<i<<' '<<j<<' '<<path<<endl;++full;goto done;}}
 if(a.hi>b.lo&&b.hi>a.lo)continue;++simple;
 if(cost<=1){++one;if(saved++<18){auto w=s.w;w.replace(a.lo,a.w.size(),a.w);w.replace(b.lo,b.w.size(),b.w);out<<cost<<' '<<id<<' '<<i<<' '<<j<<' '<<w<<endl;}}
 }}
 done:cout<<"variant_pairs "<<pairs<<" disjoint_edits "<<dis<<" induced_edges_minus_path_length_at_most_two "<<within<<" among_these_disjoint_time_intervals "<<simple<<" at_most_one_chord_disjoint_intervals "<<one<<" reached "<<full<<endl;
}
