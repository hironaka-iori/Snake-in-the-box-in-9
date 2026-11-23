#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct Alt{int defect,rep,lo,hi,rev;array<int,9> mp;vector<int>plus,minus;unsigned tie;};
int main(int argc,char**argv){
 if(argc!=5)return 2;ifstream in(argv[1]);ofstream out(argv[2]);int limit=stoi(argv[3]);mt19937 g(stoi(argv[4]));int row=0,id,c0,c1,c2,c3;string w;long long maps=0,accepted=0;
 while(row<limit &&in>>id>>c0>>c1>>c2>>c3>>w){vector<int>p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));int n=p.size();array<int,4> hit{c0,c1,c2,c3};
 set<pair<int,int>> ranges;for(int j:hit){
  for(int l=1;l<=6;l++)for(int r=1;r<=6;r++)ranges.emplace(max(0,j-l),min(n-1,j+r));
  for(int t=0;t<80;t++){int rad=9+g()%38;ranges.emplace(max(0,j-1-int(g()%rad)),min(n-1,j+1+int(g()%rad)));}
 }
 array<int,512> orig{};for(int x:p)orig[x]=1;vector<Alt> alts;set<vector<int>> seen;
 for(auto [l,r]:ranges){int len=r-l;if(len<2)continue;array<int,512> occ=orig,adj{};for(int i=l+1;i<r;i++)occ[p[i]]=0;
   for(int i=0;i<512;i++)if(occ[i])for(int d=0;d<9;d++)adj[i^(1<<d)]++;
   int delta=p[l]^p[r];array<vector<int>,2>bits;for(int i=0;i<9;i++)bits[(delta>>i)&1].push_back(i);
   int base=0;for(int k=0;k<4;k+=2)base+=((l<hit[k]&&hit[k]<r)==(l<hit[k+1]&&hit[k+1]<r));
   int nex=len<=10?84:40;
   for(int h=0;h<nex;h++){++maps;array<int,9>mp;for(int k=0;k<9;k++)mp[k]=k;
    if(h<36){int z=0;for(int a=0;a<9;a++)for(int b=0;b<a;b++,z++)if(z==h&&((delta>>a^delta>>b)&1)==0)swap(mp[a],mp[b]);}
    else if(h!=36){for(auto v:bits){auto sh=v;shuffle(sh.begin(),sh.end(),g);for(int a=0;a<(int)v.size();a++)mp[v[a]]=sh[a];}}
    int rev=(h==36||((h>36)&&g()%2));vector<int> mids;int last=rev?p[r]:p[l],cost=base-2;bool ok=true;array<int,4>newhit;
    for(int k=0;k<4;k++)newhit[k]=p[hit[k]];
    for(int i=l+1;i<r;i++){
       last^=1<<mp[w[i-1]-'0'];if(occ[last]){ok=false;break;}cost+=adj[last];if(cost>14){ok=false;break;}
       int index=rev?r-(i-l):i;for(int k=0;k<4;k++)if(hit[k]==index)newhit[k]=last;mids.push_back(last);
    }
    if(!ok)continue;int rep=0;for(int k=0;k<4;k+=2)if(popcount(unsigned(newhit[k]^newhit[k+1]))>1)rep|=1<<(k/2);
    if(!rep)continue;
    vector<int>added,removed,sorted_m=mids;sort(sorted_m.begin(),sorted_m.end());
    for(int x:mids)if(!orig[x])added.push_back(x);if(added.empty())continue;sort(added.begin(),added.end());
    for(int j=l+1;j<r;j++)if(!binary_search(sorted_m.begin(),sorted_m.end(),p[j]))removed.push_back(p[j]);sort(removed.begin(),removed.end());
    if(removed.size()!=added.size())abort();
    auto key=added;key.push_back(512);key.insert(key.end(),removed.begin(),removed.end());if(!seen.insert(key).second)continue;
    alts.push_back({cost,rep,l,r,rev,mp,added,removed,static_cast<unsigned>(g())});++accepted;
   }
 }
 sort(alts.begin(),alts.end(),[](auto&a,auto&b){return pair{a.defect,a.tie}<pair{b.defect,b.tie};});
 array<int,4> nm{};for(auto &a:alts){if(nm[a.rep]++>=42)continue;out<<id<<' '<<a.defect<<' '<<a.rep<<' '<<a.lo<<' '<<a.hi<<' '<<a.rev<<' ';for(int k:a.mp)out<<k;out<<' '<<a.plus.size();for(int x:a.plus)out<<' '<<x;for(int x:a.minus)out<<' '<<x;out<<'\n';}
 row++;
 }
 cout<<"rows "<<row<<" affine_maps "<<maps<<" distinct_eligible_variants_before_limit "<<accepted<<endl;
}
