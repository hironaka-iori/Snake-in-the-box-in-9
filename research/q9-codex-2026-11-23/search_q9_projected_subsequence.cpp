// Beam search for induced subsequences of projected higher-dimensional snakes.
#define main unused_projection_driver
#include "search_q9_project_records.cpp"
#undef main
#include <bit>
#include <cstdint>
using namespace std;
using Bits=array<uint64_t,8>;
struct Node {Bits mask{};int n=1,back=-1,score=0;};
struct Beam {
 int width,mode,best=0;long long checked=0;
 array<Bits,512> ball{};
 Beam(int w,int m):width(w),mode(m){
 for(int x=0;x<512;x++)for(int d=-1;d<9;d++){int v=d<0?x:x^(1<<d);ball[x][v/64]|=1ULL<<(v%64);}
 }
 bool test(const Path&p,int row,int cut,int rev){
 vector<vector<Node>> live(p.size());vector<pair<int,int>> parents;
 array<Path,512> pos;vector<Bits> future(p.size()+1);
 for(int i=int(p.size())-1;i>=0;i--){future[i]=future[i+1];future[i][p[i]/64]|=1ULL<<(p[i]%64);}
 for(int i=0;i<int(p.size());i++)pos[p[i]].push_back(i);
 for(int i=0;i<int(p.size());i++){
  auto&v=live[i];v.emplace_back();
  sort(v.begin(),v.end(),[](const Node&a,const Node&b){if(a.score!=b.score)return a.score>b.score;if(a.n!=b.n)return a.n>b.n;return a.mask<b.mask;});
  vector<Node> keep;for(auto &s:v){if(!keep.empty()&&s.mask==keep.back().mask&&s.n==keep.back().n)continue;
   keep.push_back(s);if((int)keep.size()==width)break;}vector<Node>().swap(v);
  for(auto &s:keep){
   int link=parents.size();parents.emplace_back(p[i],s.back);
   if(s.n-1>best){best=s.n-1;
    if(best>=185){Path out;for(int j=link;j>=0;j=parents[j].second)out.push_back(parents[j].first);
     reverse(out.begin(),out.end());if(!Search::valid(out,9))abort();
     cout<<"BEST "<<best<<" row "<<row<<" cut "<<cut<<" rev "<<rev<<" path";for(int x:out)cout<<' '<<x;cout<<endl;}
    if(best>=192)return true;
   }
   Bits mask=s.mask;for(int h=0;h<8;h++)mask[h]|=ball[p[i]][h];
   for(int k=0;k<9;k++){int x=p[i]^(1<<k);if((s.mask[x/64]>>(x%64))&1)continue;
    auto &a=pos[x];auto it=upper_bound(a.begin(),a.end(),i);if(it==a.end())continue;
    // Earliest next occurrence can realize any continuation from a later occurrence.
    int j=*it,space=0;for(int h=0;h<8;h++)space+=popcount(future[j][h]&~mask[h]);
    if(s.n+space<min(best,191))continue;
    live[j].push_back({mask,s.n+1,link,mode*(s.n+1)+space});++checked;
   }
  }
 }
 return false;
 }
};
int main(int argc,char**argv){
 if(argc!=6)return 2;Beam b(stoi(argv[1]),stoi(argv[2]));int lo=stoi(argv[3]),hi=stoi(argv[4]),cap=stoi(argv[5]),row=0,maps=0;
 string line;while(getline(cin,line)){if(++row<lo)continue;if(row>hi)break;
  auto a=line.find(','),y=line.find(',',a+1),z=line.find(',',y+1);int n=stoi(line.substr(0,a));
  array<int,16> freq{};istringstream in(line.substr(y+1,z-y-1));int k;Path d;
  while(in>>k){d.push_back(k);++freq[k];}
  vector<pair<int,int>> masks;for(int m=0;m<(1<<n);m++)if(popcount((unsigned)m)==n-9){
   int f=0;for(int j=0;j<n;j++)if(m>>j&1)f+=freq[j];masks.emplace_back(f,m);}sort(masks.begin(),masks.end());
  for(int j=0;j<(int)masks.size()&&j<cap;j++){
   int cut=masks[j].second,lab=0;array<int,16> axes{};for(int h=0;h<n;h++)if(!(cut>>h&1))axes[h]=1<<lab++;
   Path p{0};for(int e:d)if(axes[e])p.push_back(p.back()^axes[e]);
   for(int r:{0,1}){if(b.test(p,row,cut,r))return 0;reverse(p.begin(),p.end());}++maps;
  }
  if(row%8==0)cerr<<"progress row "<<row<<" maps "<<maps<<" best "<<b.best<<endl;
 }
 cerr<<"DONE maps "<<maps<<" proposals "<<b.checked<<" best "<<b.best<<endl;
}
