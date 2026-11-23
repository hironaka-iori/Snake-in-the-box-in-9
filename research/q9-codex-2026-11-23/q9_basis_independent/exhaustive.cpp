// Exhaust independent generator sets directly in the original labels. No parity
// forms or transformation into coordinates; a precomputed 3-axis obstruction
// excludes triples that would give a compulsory vertex three neighbours.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Mask{
  array<uint64_t,8> z{};
  void put(int v){z[v/64]|=uint64_t(1)<<(v%64);}
  void subtract(const Mask& m){for(int k=0;k<8;k++)z[k]&=~m.z[k];}
  int pop(){for(int k=0;k<8;k++)if(z[k]){int b=countr_zero(z[k]);z[k]&=z[k]-1;return 64*k+b;}return 512;}
};
Mask forbidden[511][511];
struct Test{
  vector<int> p;array<int,512> weight{},inc{};array<int,511> dir{};int n,h;
  vector<int> chosen,expected;vector<Mask> touch;
  unsigned long long nodes=0,ranked=0,final_graphs=0,addsets=0;
  Test(vector<int> q,int holes):p(q),n(q.size()),h(holes){
    for(int x:p)inc[x]=1;
    iota(dir.begin(),dir.end(),1);
    for(int g:dir)for(int x:p)weight[g]+=inc[x^g];for(int& e:weight)e/=2;
    sort(dir.begin(),dir.end(),[&](int a,int b){return pair(weight[a],a)<pair(weight[b],b);});
    touch.resize(n);
    for(int j=0;j<n;j++)for(int i=0;i<511;i++)if(inc[p[j]^dir[i]])touch[j].put(i);
    for(int a=0;a<511;a++)for(int b=a+1;b<511;b++){
      Mask v;
      for(int j=0;j<n;j++)if(inc[p[j]^dir[a]]&&inc[p[j]^dir[b]])
        for(int k=0;k<8;k++)v.z[k]|=touch[j].z[k];
      forbidden[a][b]=v;
    }
  }
  bool trace(const vector<int>&bs){
    int tip=-1,selected=0,tips=0;array<int,512> d{};
    for(int x=0;x<512;x++)if(inc[x]){selected++;for(int g:bs)d[x]+=inc[x^g];if(d[x]>2||!d[x])return false;if(d[x]==1){tip=x;tips++;}}
    if(tips!=2)return false;vector<int> ordered;int prev=-1,x=tip;
    while(x!=-1){ordered.push_back(x);int next=-1;for(int g:bs)if((x^g)!=prev&&inc[x^g]){next=x^g;break;}prev=x;x=next;}
    if(ordered.size()!=selected)return false;expected=ordered;return true;
  }
  bool final(int edges){
    vector<int> span{0},bs;array<bool,512> known{};known[0]=true;
    for(int i:chosen){int g=dir[i];if(known[g])return false;int len=span.size();for(int k=0;k<len;k++){int v=span[k]^g;known[v]=true;span.push_back(v);}bs.push_back(g);}
    ranked++;
    if(!h){final_graphs++;return trace(bs);}
    vector<pair<int,int>> extra;
    array<int,512> d{};
    for(int x:p)for(int g:bs)d[x]+=inc[x^g];
    for(int y=0;y<512;y++)if(!inc[y]){
      int cnt=0;bool ok=true;for(int g:bs)if(inc[y^g]){cnt++;if(d[y^g]>=2)ok=false;}
      if(ok&&cnt<=2)extra.emplace_back(y,cnt);
    }
    int want=n+h-1-edges;
    for(int j=0;j<extra.size();j++){auto[x,ex]=extra[j];inc[x]=1;
      if(h==1){if(ex==want){addsets++;if(trace(bs))return true;}}
      else for(int k=0;k<j;k++){auto[y,ey]=extra[k];int touch=find(bs.begin(),bs.end(),x^y)!=bs.end();if(ex+ey+touch!=want)continue;
        addsets++;inc[y]=1;if(trace(bs))return true;inc[y]=0;
      }
      inc[x]=0;
    }
    return false;
  }
  bool search(Mask opts,int e){
    nodes++;int need=9-chosen.size();Mask copy=opts;vector<int> valid;
    for(int i=copy.pop();i<511;i=copy.pop())valid.push_back(i);
    if(valid.size()<need)return false;
    int high=e;for(int k=0;k<need;k++)high+=weight[dir[valid[valid.size()-1-k]]];
    if(high<n-h-1)return false;
    for(int j=0;j+need<=valid.size();j++){
      int i=opts.pop();int low=e;for(int k=j;k<j+need;k++)low+=weight[dir[valid[k]]];if(low>n-1)break;
      int e2=e+weight[dir[i]];Mask next=opts;for(int prev:chosen)next.subtract(forbidden[prev][i]);
      chosen.push_back(i);bool ok=need==1?(e2>=n-1-h&&final(e2)):search(next,e2);if(ok)return true;chosen.pop_back();
    }return false;
  }
  void run(int row){Mask m;for(int i=0;i<511;i++)m.put(i);bool result=search(m,0);
    cout<<"ROW "<<row<<" "<<(result?"FOUND":"CLOSED")<<" nodes "<<nodes<<" ranked "<<ranked<<" direct "<<final_graphs<<" hole_sets "<<addsets;
    if(result){cout<<" basis";for(int i:chosen)cout<<" "<<dir[i];cout<<" path";for(int x:expected)cout<<" "<<x;}cout<<endl;
  }
};
int main(int argc,char**argv){if(argc!=2)return 2;int h=stoi(argv[1]);if(h<0||h>2)return 2;string line;int row=0;while(getline(cin,line)){
  istringstream ss(line);int x;vector<int> p;while(ss>>x)p.push_back(x);Test(p,h).run(row++);
}}
