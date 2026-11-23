#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <string>
#include <vector>
using namespace std;
using B=bitset<192>;using P=vector<int>;using M=array<int,9>;
struct Bank{string word;P p;array<B,512> near{};map<int,set<string>> shapes;};
string shape(string s){auto norm=[](const string&a){int lab[9]={},k=0;string z;for(auto c:a){int d=c-'0';if(!lab[d])lab[d]=++k;z+='0'+lab[d]-1;}return z;};auto f=norm(s);reverse(s.begin(),s.end());return min(f,norm(s));}
struct G{int cost,row,donor,a,b,s,e,gain;M map;B conflicts;};
int main(int argc,char**argv){
 if(argc!=3)return 2;int tries=stoi(argv[1]);mt19937 rng(stoi(argv[2]));
 vector<Bank> bank;string w;while(cin>>w){Bank t;t.word=w;t.p={0};for(char c:w)t.p.push_back(t.p.back()^(1<<(c-'0')));if(t.p.size()!=192)return 3;
  for(int i=0;i<192;i++){int v=t.p[i];t.near[v].set(i);for(int d=1;d<512;d*=2)t.near[v^d].set(i);}bank.push_back(std::move(t));}
 int N=bank.size();vector<vector<G>> bins(N*4*5);long long fitted=0,embedded=0,rejectshape=0;
 for(int t=0;t<tries;t++){
  int r=rng()%N,z=rng()%N;if(r==z)continue;auto &h=bank[r],&donor=bank[z];
  int g=2*(1+rng()%4),len=12+rng()%44,dl=len+g,a=1+rng()%(190-len),b=a+len;
  int H=h.p[a]^h.p[b],s=0,e=0,D=0;bool match=false;
  for(int rep=0;rep<16;rep++){s=rng()%(192-dl);e=s+dl;if(rng()%2)swap(s,e);D=donor.p[s]^donor.p[e];if(popcount(unsigned(H))==popcount(unsigned(D))){match=true;break;}}
  if(!match)continue;fitted++;
  int sign=e>s?1:-1;
  auto step=[&](int j){return int(donor.word[(sign>0?s+j:s-j-1)]-'0');};
  int votes[9][9]={};for(int j=0;j<len;j++){
   int k=h.word[a+j]-'0';votes[step(j)][k]+=j<9?5:1;votes[step(dl-1-j)][h.word[b-1-j]-'0']+=j<9?5:1;
   votes[step(j*dl/len)][k]+=2;
  }
  int bias=(t%7==0?0:1);M mp;mp.fill(-1);int used=0;
  for(int k=0;k<9;k++){
   int src=-1,dst=-1,top=-1;for(int x=0;x<9;x++)if(mp[x]<0)for(int y=0;y<9;y++)if(!(used>>y&1)&&((H>>y&1)==(D>>x&1))){
    int value=votes[x][y]*bias*9+rng()%20;if(value>top){src=x;dst=y;top=value;}
   }mp[src]=dst;used|=1<<dst;
  }
  B outside;for(int j=0;j<a;++j)outside.set(j);for(int j=b+1;j<192;j++)outside.set(j);
  auto &bin=bins[(r*4+g/2-1)*5+min(4,a/38)];int threshold=bin.size()>=5?bin.back().cost:45;
  int v=h.p[a];B hit;for(int j=0;j<dl-1;++j){v^=1<<mp[step(j)];hit|=h.near[v];}
  if((v^(1<<mp[step(dl-1)]))!=h.p[b])abort();embedded++;
  hit&=outside;int cost=hit.count();if(cost>threshold||(!bin.empty()&&bin.size()==5&&cost==threshold))continue;
  auto it=h.shapes.find(dl);if(it==h.shapes.end()){set<string> indexed;for(int i=0;i+dl<=191;i++)indexed.insert(shape(h.word.substr(i,dl)));it=h.shapes.emplace(dl,std::move(indexed)).first;}
  if(it->second.count(shape(donor.word.substr(min(e,s),dl)))){rejectshape++;continue;}
  G cand{cost,r,z,a,b,s,e,g,mp,hit};bool dup=false;for(auto &old:bin)if(old.a==a&&old.b==b&&old.conflicts==hit)dup=true;if(dup)continue;
  bin.push_back(cand);stable_sort(bin.begin(),bin.end(),[](auto &x,auto&y){return x.cost<y.cost;});if(bin.size()>5)bin.pop_back();
 }
 int n=0;for(auto &bin:bins)for(auto &x:bin){cout<<"G "<<x.row<<" "<<x.donor<<" "<<x.a<<" "<<x.b<<" "<<x.s<<" "<<x.e<<" ";for(int t:x.map)cout<<t;cout<<" "<<x.cost<<"\n";n++;}
 cerr<<"DONE draws "<<tries<<" endpoint_matched "<<fitted<<" mapped "<<embedded<<" rejected_non_novel_at_ranking "<<rejectshape<<" kept "<<n<<endl;
}
