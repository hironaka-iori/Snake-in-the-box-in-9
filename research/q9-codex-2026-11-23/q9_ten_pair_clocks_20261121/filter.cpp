#include <algorithm>
#include <array>
#include <cassert>
#include <bit>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
struct Layout{array<int,10>grp,axis;};
vector<Layout> layouts;
void parts(vector<int> a,vector<pair<int,int>> p){
 if(a.empty()){for(int s=0;s<5;s++){Layout l;int g=0;for(int j=0;j<5;j++){auto[x,y]=p[j];if(j==s){l.grp[x]=l.grp[y]=4;l.axis[x]=l.axis[y]=8;}else{l.grp[x]=l.grp[y]=g;l.axis[x]=2*g;l.axis[y]=2*g+1;g++;}}layouts.push_back(l);}return;}
 int x=a[0];for(int k=1;k<(int)a.size();k++){auto b=a;int y=b[k];b.erase(b.begin()+k);b.erase(b.begin());auto q=p;q.push_back({x,y});parts(b,q);}
}
struct State{array<int,32>cnt{};array<int,160>edges{},twA{},twB{};int bad=0;};
struct Item{int row,start,layout,defect=-1;string grouped,mapped;};
int pairid(int f,int h){return (f&~(1<<h))*5+h;}
int status(const State&s){
 if(s.bad)return 0;
 for(int z:s.cnt)if(z>16)return 1;
 for(int f=0;f<32;f++)for(int h=0;h<5;h++)if(!(f>>h&1)){int n=s.cnt[f],m=s.cnt[f^(1<<h)],ix=5*f+h,e=s.edges[ix],a=s.twA[ix],b=s.twB[ix];
 if(h==4){if(n+m-e>16)return 2;}else if(e-a-b+(n-e+a+1)/2+(m-e+b+1)/2>8)return 3;
 }return 4;
}
string key(string w){auto normalize=[](string s){array<char,5>m{};char next='0';for(char &c:s){int d=c-'0';if(d==4)continue;if(!m[d])m[d]=next++;c=m[d];}return s;};string s=normalize(w);reverse(w.begin(),w.end());return min(s,normalize(w));}
int flaws(const string&w){array<int,512>seen{};int x=0,n=0;seen[0]++;for(char c:w){x^=1<<(c-'0');n+=seen[x]++;for(int j=0;j<9;j++)n+=seen[x^(1<<j)];--n;}return n;}
int main(int argc,char**argv){
 if(argc!=9&&argc!=10)return 2;ofstream ranges;if(argc==10)ranges.open(argv[9]);int len=stoi(argv[2]),rows=stoi(argv[3]),stride=stoi(argv[4]),keep=stoi(argv[5]),seed=stoi(argv[6]),nlay=stoi(argv[7]);mt19937 rng(seed);
 vector<int>dims(10);iota(dims.begin(),dims.end(),0);parts(dims,{});assert(layouts.size()==4725);vector<int> ids(4725);iota(ids.begin(),ids.end(),0);if(nlay<4725){shuffle(ids.begin(),ids.end(),rng);ids.resize(nlay);}
 ifstream f(argv[1]);ofstream out(argv[8]);string line;long long counts[5]{},pass=0;vector<Item>sample;int row=0;
 while(row<rows&&getline(f,line)){istringstream is(line);int dim,v;is>>dim;vector<int>p,w;while(is>>v)p.push_back(v);for(int i=1;i<(int)p.size();i++)w.push_back(countr_zero((unsigned)(p[i]^p[i-1])));
 for(int li:ids){const Layout&l=layouts[li];int n=w.size();if(n<len)continue;vector<int>g(n),h(n+1),ed(n),da(n),db(n),bad(n);
 for(int i=0;i<n;i++){g[i]=l.grp[w[i]];h[i+1]=h[i]^1<<g[i];ed[i]=pairid(h[i],g[i]);
 if(i&&g[i]==g[i-1]){if(h[i]>>g[i]&1)db[i]=1;else da[i]=1;}
 if(i&&g[i]==4&&(g[i-1]==4||(i>=2&&g[i-2]==4)))bad[i]=1;
 if(i>=2&&g[i]==g[i-1]&&g[i]==g[i-2])bad[i]=1;}
 vector<int>passed;State s;for(int i=0;i<=len;i++)s.cnt[h[i]]++;for(int i=0;i<len;i++){s.edges[ed[i]]++;if(i){s.twA[ed[i]]+=da[i];s.twB[ed[i]]+=db[i];}}
 // Keep exact interval containment for the local word obstructions.
 vector<int>b2(n+1),b3(n+1);for(int i=0;i<n;i++){b2[i+1]=b2[i]+(i&&g[i]==4&&g[i-1]==4);b3[i+1]=b3[i]+(i>=2&&(g[i]==4&&g[i-2]==4||g[i]==g[i-1]&&g[i]==g[i-2]));}
 for(int st=0;st+len<=n;st++){int en=st+len;s.bad=b2[en]-b2[st+1]+b3[en]-b3[st+2];
 if(st%stride==0){int r=status(s);counts[r]++;if(r==4){if(ranges.is_open())passed.push_back(st);++pass;int slot=-1;if((int)sample.size()<keep)slot=sample.size();else{long long u=uniform_int_distribution<long long>(0,pass-1)(rng);if(u<keep)slot=u;}
 if(slot>=0){Item it{row,st,li};for(int t=st;t<en;t++){it.grouped+=char('0'+g[t]);it.mapped+=char('0'+l.axis[w[t]]);}it.defect=flaws(it.mapped);if(slot==(int)sample.size())sample.push_back(move(it));else sample[slot]=move(it);}}}
 if(en==n)break;s.cnt[h[st]]--;s.cnt[h[en+1]]++;s.edges[ed[st]]--;s.edges[ed[en]]++;s.twA[ed[st+1]]-=da[st+1];s.twB[ed[st+1]]-=db[st+1];s.twA[ed[en]]+=da[en];s.twB[ed[en]]+=db[en];}
 if(ranges.is_open()&&!passed.empty()){ranges<<row<<' '<<li<<' ';for(int x:l.axis)ranges<<x;ranges<<' ';for(int u:w)ranges<<l.axis[u];ranges<<' ';for(int i=0;i<(int)passed.size();){int j=i;while(j+1<(int)passed.size()&&passed[j+1]==passed[j]+1)j++;ranges<<passed[i]<<'-'<<passed[j]<<',';i=j+1;}ranges<<'\n';}
 }row++;
 }
 set<string> seen;sort(sample.begin(),sample.end(),[](auto&a,auto&b){return a.defect<b.defect;});for(auto&i:sample){if(!seen.insert(key(i.grouped)).second)continue;out<<i.row<<' '<<i.start<<' '<<i.layout<<' ';for(auto d:layouts[i.layout].axis)out<<d;out<<' '<<i.defect<<' '<<i.grouped<<' '<<i.mapped<<'\n';}
 cout<<"rows "<<row<<" target "<<len<<" layouts_per_row "<<ids.size()<<" starts_stride "<<stride<<" axis_windows "<<accumulate(counts,counts+5,0LL)<<" short_forced "<<counts[0]<<" single_fiber "<<counts[1]<<" across_single "<<counts[2]<<" across_pair "<<counts[3]<<" survive "<<counts[4]<<" retained_unique_in_sample "<<seen.size()<<endl;
}
