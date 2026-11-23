#define main old_cut_driver
#include "cuts.cpp"
#undef main
#include <random>
int main(){vector<string>rows;string w;while(cin>>w)rows.push_back(w);mt19937 rng(73411);
 for(int rep=0;rep<150000;rep++){int r=rng()%rows.size();auto s=rows[r];V p{0},A;for(char c:s)p.push_back(p.back()^(1<<(c-'0')));for(int i=0;i<p.size();i+=2)A.push_back(p[i]);
  int j=1+2*(rng()%95);int mid=p[j],x=p[j-1],y=p[j+1];int b=mid^(1<<(rng()%9));if(find(A.begin(),A.end(),b)!=A.end())continue;int idx=rng()%A.size(),lost=A[idx];if(lost==x||lost==y)continue;A[idx]=b;H h(A);if(!h.old||h.assess({}).components!=1)continue;
  for(int c:h.branch){if(A[c]==b||A[c]==x||A[c]==y)continue;auto ev=h.assess({c});if(ev.delta<1)continue;
   V q{h.slot[x]};vector<bool>vis(A.size());vis[c]=true;vis[h.slot[x]]=true;for(int k=0;k<q.size();k++)for(int z:h.adj[q[k]])if(!vis[z]){vis[z]=true;q.push_back(z);}
   if(vis[h.slot[y]])continue;cout<<r<<" "<<mid<<" "<<x<<" "<<y<<" "<<b<<" "<<lost<<" "<<A[c]<<" "<<ev.components<<" "<<ev.endpoint_need<<endl;return 0;
  }
 }return 3;
}
