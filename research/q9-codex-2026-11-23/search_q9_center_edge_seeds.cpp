#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <set>
#include <sstream>
#include <vector>
// Input lines contain independently valid Q9 paths in vertex order.
// Extract subpaths that lift to a centrally edge-symmetric snake.
using namespace std;
using Row = array<unsigned char,512>;
int main(int argc,char**argv) {
  if(argc!=3)return 2;
  int threshold=stoi(argv[1]), limit=stoi(argv[2]);
  string line;
  set<vector<int>> seeds;
  long long checks=0;
  int best=0,read=0;
  while(read<limit && getline(cin,line)) {
    istringstream input(line);
    int x;
    vector<int> path;
    while(input>>x)path.push_back(x);
    if(path.size()<threshold+1 || path.size()>254)continue;
    array<int,512> idx;idx.fill(-1);
    for(int i=0;i<path.size();i++) {
      x=path[i];
      if(x<0||x>=512||idx[x]>=0)return 3;
      for(int j=0;j<i;j++)if((__builtin_popcount(path[j]^x)==1)!=(j+1==i))return 3;
      idx[x]=i;
    }
    ++read;
    for(int direction=0;direction<2;direction++,reverse(path.begin(),path.end())) {
      int n=path.size();
      // near[i][v] is the earliest index >= i occupied by v or a neighbor.
      vector<Row> near(n+1); near[n].fill(255);
      for(int i=n-1;i>=0;i--) {
        near[i]=near[i+1];near[i][path[i]]=i;
        for(int j=0;j<9;j++)near[i][path[i]^(1<<j)]=i;
      }
      array<int,9> pi;iota(pi.begin(),pi.end(),0);
      do {
        bool inv=true;
        int t=0;
        for(int i=0;i<9;i++){inv &= pi[pi[i]]==i;t+=pi[i]>i;}
        if(!inv||t<2)continue;
        array<int,512> m{};
        for(int v=1;v<512;v++)m[v]=m[v&(v-1)]^(1<<pi[__builtin_ctz(v)]);
        for(int a=0;a<9;a++)if(pi[a]==a) {
          array<int,9> label{};int count=0;
          for(int i=0;i<9;i++)if(pi[i]>i){label[i]=count++;label[pi[i]]=count++;}
          for(int i=0;i<9;i++)if(pi[i]==i && i!=a)label[i]=count++;
          label[a]=8;
          for(int i=0;i+threshold<n;i++) {
            ++checks;
            int phase=m[path[i]]^path[i]^(1<<a),k=i+1;
            for(;k<n;k++)if(near[i][m[path[k]]^phase]<=k)break;
            int length=k-i-1;
            best=max(best,length);
            if(length<threshold)continue;
            vector<int> seed{t,0};int v=0;
            for(int j=i+1;j<k;j++) {
              v^=1<<label[__builtin_ctz(path[j]^path[j-1])];seed.push_back(v);
            }
            seeds.insert(seed);
          }
        }
      }while(next_permutation(pi.begin(),pi.end()));
    }
  }
  for(auto &row:seeds){for(int v:row)cout<<v<<" ";cout<<"\n";}
  cerr<<"paths "<<read<<" center tests "<<checks<<" best half "<<best<<" seeds "<<seeds.size()<<"\n";
}
