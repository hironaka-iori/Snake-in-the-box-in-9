// Keep the transitions inside each block; choose each connecting edge independently.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <fstream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using P=vector<int>;
set<string> known;
string shape(const P& p){
 string w;for(int j=1;j<p.size();j++)w+=char('0'+countr_zero((unsigned)(p[j]^p[j-1])));
 auto code=[](string w){array<int,9>ids;ids.fill(-1);int n=0;for(char&c:w){auto&x=ids[c-'0'];if(x<0)x=n++;c='0'+x;}return w;};auto a=code(w);reverse(w.begin(),w.end());return min(a,code(w));
}
struct Search{
 P p,cut,off,result;
 array<int,512> used{},touch{};
 int count=0,cap; long long nodes=0;
 void place(int k,int m,int sign){off[k]=m;for(int i=cut[k];i<cut[k+1];i++){
  int v=p[i]^m;used[v]+=sign;for(int b=0;b<9;b++)touch[v^(1<<b)]+=sign;}}
 P options(int k,bool left){P choices;int a=left?cut[k+1]-1:cut[k],b=left?a+1:a-1;
  for(int d=0;d<9;d++){int m=p[a]^p[b]^off[k+(left?1:-1)]^(1<<d);bool ok=true;
   for(int i=cut[k];i<cut[k+1];i++){int v=p[i]^m;if(used[v]||touch[v]!=(i==a)){ok=false;break;}}
   if(ok)choices.push_back(m);}
  return choices;}
 bool dfs(int lo,int hi){
  if(++nodes>cap)return false;
  if(lo==0&&hi+2==(int)cut.size()){result=p;for(int k=0;k+1<cut.size();k++)for(int i=cut[k];i<cut[k+1];i++)result[i]^=off[k];return known.empty()||!known.count(shape(result));}
  P l,r;if(lo>0){l=options(lo-1,true);if(l.empty())return false;}
  if(hi+2<cut.size()){r=options(hi+1,false);if(r.empty())return false;}
  bool left=r.empty()||(!l.empty()&&l.size()<=r.size());int k=left?lo-1:hi+1;
  for(int m:(left?l:r)){place(k,m,1);if(dfs(min(lo,k),max(hi,k)))return true;place(k,m,-1);if(nodes>cap)break;}
  return false;
 }
 bool run(){off.assign(cut.size(),0);int mid=0;for(int i=1;i+1<cut.size();i++)if(cut[i+1]-cut[i]>cut[mid+1]-cut[mid])mid=i;
  place(mid,0,1);return dfs(mid,mid);}
};
bool valid(P const&p){set<int>s(p.begin(),p.end());if(s.size()!=p.size())return false;
 for(int j=1;j<p.size();j++)for(int i=0;i<j;i++)if((popcount((unsigned)(p[i]^p[j]))==1)!=(i+1==j))return false;return true;}
int main(int argc,char**argv){
 if(argc!=5&&argc!=6)return 2;if(argc==6){ifstream f(argv[5]);string w;while(f>>w)known.insert(w);if(known.size()!=131)return 7;}mt19937 gen(stoul(argv[1]));int trials=stoi(argv[2]),cap=stoi(argv[3]),expected=stoi(argv[4]);
 vector<P>bank;vector<vector<pair<int,int>>> flaws;string line;
 while(getline(cin,line)){istringstream ss(line);int v;P p;while(ss>>v){if(v<0||v>=512)return 3;p.push_back(v);}if(p.size()!=expected+1)continue;vector<pair<int,int>>bad;
 for(int j=1;j<p.size();j++){if(popcount((unsigned)(p[j]^p[j-1]))!=1)return 4;for(int i=0;i+1<j;i++)if(popcount((unsigned)(p[i]^p[j]))<2)bad.emplace_back(i,j);}
 bank.push_back(p);flaws.push_back(bad);}if(bank.empty())return 5;
 long long nodes=0,lim=0;for(int it=0;it<trials;it++){int k=gen()%bank.size(),n=expected+1;auto&p=bank[k];set<int>cuts{0,n};
 for(auto [i,j]:flaws[k])cuts.insert(i+1+gen()%(j-i));int extra=6+gen()%35;
 for(int h=0;h<extra;h++){int pos=1+gen()%(n-1);cuts.insert(pos);if(gen()%5==0&&pos<n-1)cuts.insert(pos+1);}
 Search s;s.p=p;s.cut.assign(cuts.begin(),cuts.end());s.cap=cap;
 if(s.run()){if(!valid(s.result))abort();if(known.empty()){cout<<"FOUND "<<expected<<" vertices";for(int v:s.result)cout<<" "<<v;cout<<endl;return 0;}
 known.insert(shape(s.result));cout<<"NEW "<<expected<<" vertices";for(int v:s.result)cout<<" "<<v;cout<<endl;
 for(int h=0;h<2;h++,reverse(s.result.begin(),s.result.end()))for(int b=0;b<9;b++){P w=s.result;w.push_back(w.back()^(1<<b));if(valid(w)){cout<<"FOUND "<<expected+1<<" vertices";for(int v:w)cout<<" "<<v;cout<<endl;return 0;}}}
 nodes+=s.nodes;lim+=s.nodes>cap;
 if((it+1)%10000==0)cout<<"STEP "<<it+1<<" capped "<<lim<<" nodes "<<nodes<<endl;
 }cout<<"DONE "<<trials<<" capped "<<lim<<" nodes "<<nodes<<endl;
}

