#define main straight_segment_main
#include "search_q9_segment_free_tips.cpp"
#undef main
#include <random>

int main(int argc, char **argv) {
 if(argc != 4) return 2;
 target=atoi(argv[1]);
 const int trials=atoi(argv[2]);
 mt19937 rng(atoi(argv[3]));
 trim=24; cap=60000;
 int seeds=0; string line;
 while(getline(cin,line)) {
  istringstream input(line); vector<int> path; int x;
  while(input>>x)path.push_back(x);
  const int n=path.size();
  if(n!=193)abort();
  array<int,512> pos; pos.fill(-1);
  int a=-1,b=-1;
  for(int k=0;k<n;k++) {
   if(path[k]<0||path[k]>=512||pos[path[k]]>=0)abort();
   if(k&&__builtin_popcount(path[k]^path[k-1])!=1)abort();
   for(int d=0;d<9;d++) {
    int h=pos[path[k]^(1<<d)];
    if(h>=0&&h<k-1){if(a!=-1)abort();a=h;b=k;}
   }
   pos[path[k]]=k;
  }
  if(a<0)abort();
  seeds++;
  for(int trial=0;trial<trials;trial++) {
   int i=1+rng()%(n-3),j=i+1+rng()%(n-2-i);
   if(j-i<4||((i<=a&&a<=j)==(i<=b&&b<=j)))continue;
   // Permute axes separately in the support and complement of the anchor difference.
   array<int,9> perm;for(int d=0;d<9;d++)perm[d]=d;
   int diff=path[i]^path[j];
   for(int h=0;h<trial%7;h++) {
    int d=rng()%9,e=rng()%9;
    if(((diff>>d)^(diff>>e))&1)continue;
    swap(perm[d],perm[e]);
   }
   intervals++;
   vector<int> q(path);
   int left=0,right=0,changed=0;
   for(int k=i+1;k<=j;k++) {
    int originalStep=path[i+j-k+1]^path[i+j-k];
    q[k]=q[k-1]^(1<<perm[__builtin_ctz(originalStep)]);
    changed+=q[k]!=path[k];
    for(int axis=-1;axis<9;axis++) {
     int h=pos[q[k]^(axis<0?0:1<<axis)];
     if(h<0||(i<=h&&h<=j)||(k==j&&h==j+1&&axis>=0))continue;
     if(h<i)left=max(left,h+1);else right=max(right,n-h);
    }
    if(left+right>trim)break;
   }
   if(left+right>trim||changed<3)continue;
   if(q[j]!=path[j])abort();
   // The fixed start anchor can itself be the end of the input chord.
   if(a==i&&b>j)right=max(right,n-b);
   if(b==i&&a<i)left=max(left,a+1);
   if(left+right>trim||left>i||right>n-1-j)continue;
   legal++;
   for(int l=left;l<=min(i,left+3);l++)for(int r=right;r<=min(n-1-j,right+3)&&l+r<=trim;r++) {
    string key;
    for(int k=l+1;k<n-r;k++)key+=char(__builtin_ctz(q[k]^q[k-1]));
    if(!seen.insert(key).second)continue;
    Growth g;
    for(int k=l;k<n-r;k++){g.path.push_back(q[k]);g.toggle(q[k],1);}
    g.dfs(false);nodes+=g.visits;bodies++;capped+=g.limited;
   }
  }
 }
 cout<<"seeds "<<seeds<<" trials_per_seed "<<trials<<" tested "<<intervals<<" repairable "<<legal
 <<" distinct_bodies "<<bodies<<" nodes "<<nodes<<" capped "<<capped<<" best_edges "<<best<<endl;
}
