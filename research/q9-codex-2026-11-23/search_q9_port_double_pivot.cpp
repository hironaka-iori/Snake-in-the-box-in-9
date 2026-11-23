// Enumerate all two-pivot cuts with a minimum segment length.
#define main random_hinge_driver
#include "search_q9_two_independent_hinges.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=3)return 2;int minpart=atoi(argv[1]),cap=atoi(argv[2]),batch=100000;
 vector<vector<int>> paths;vector<vector<pair<int,int>>> defects;string line;long long nodes=0,joins=0,complete=0,limited=0,filtered=0,attempted=0,pairs=0;
 while(getline(cin,line)){istringstream s(line);int x;vector<int>p;while(s>>x){if(x<0||x>=512)abort();p.push_back(x);}if(p.empty())continue;
  vector<pair<int,int>> bad;for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){if(p[i]==p[j]||(i==j+1&&popcount((unsigned)(p[i]^p[j]))!=1))abort();if(j+1<i&&popcount((unsigned)(p[i]^p[j]))==1)bad.push_back({j,i});}
  paths.push_back(p);defects.push_back(bad);
 }
 for(int k=0;k<(int)paths.size();k++){auto &source=paths[k];int n=source.size()-1;
 for(int lo=minpart;lo<=n-2*minpart;lo++)for(int hi=lo+minpart;hi<=n-minpart;hi++){
 auto &p=source;
  auto internal=[&](int a,int b){for(auto [i,j]:defects[k])if(a<=i&&j<=b)return true;return false;};
  if(internal(0,lo)||internal(lo,hi)||internal(hi,n)){filtered++;continue;}
  attempted++;Tail left(p,lo,hi,true,cap),right(p,lo,hi,false,cap);
  auto*l=&left,*r=&right;if(lo<n-hi)swap(l,r);
  l->visit(0,511);if(!l->opts.empty())r->visit(0,511);nodes+=l->nodes+r->nodes;
  if(l->limited||r->limited)limited++;else complete++;
  if(!l->opts.empty()&&!r->opts.empty())pairs++;
  for(auto &a:left.opts)for(auto &b:right.opts){joins++; if(intersects(a.boundary,b.points))continue;
   for(int i=0;i<lo;i++)p[i]=p[lo]^moved(p[i]^p[lo],a.image);for(int i=hi+1;i<=n;i++)p[i]=p[hi]^moved(p[i]^p[hi],b.image);
   if(!valid(p))abort();cout<<"FOUND "<<n<<" "<<lo<<" "<<hi<<" vertices";for(int x:p)cout<<" "<<x;cout<<endl;return 0;
  }
  if(attempted%batch==0)cout<<"progress "<<k<<" eligible "<<attempted<<" complete "<<complete<<" capped "<<limited<<" candidates_both "<<pairs<<" joins "<<joins<<" nodes "<<nodes<<endl;
 }
 }
 cout<<"DONE eligible "<<attempted<<" complete "<<complete<<" capped "<<limited<<" filtered "<<filtered<<" candidates_both "<<pairs<<" joins "<<joins<<" nodes "<<nodes<<endl;
}
