// Use the same verified permutation pruning as the single-pivot search.
#define main single_pivot_main
#include "search_q9_pivot.cpp"
#undef main
#include <set>
#include <cstdlib>
vector<int> canonical(const vector<int>&b,int start,int dir,int len){
  array<int,9> labels; labels.fill(-1);int count=0;vector<int>v{0};
  for(int i=0;i<len;i++){int t=start+dir*i;
    int axis=countr_zero(unsigned(b[t]^b[t+dir]));if(labels[axis]<0)labels[axis]=count++;
    v.push_back(v.back()^(1<<labels[axis]));}
  return v;
}
int main(int argc,char**argv){
  if(argc<4)return 2;
  int arm=atoi(argv[1]),stride=atoi(argv[2]),offset=atoi(argv[3]);
  if(arm<1||arm>=192||stride<1||offset<0)return 2;
  set<vector<int>> arms;vector<int>b(192);
  while(cin>>b[0]){for(int i=1;i<192;i++)if(!(cin>>b[i]))return 3;
    if(!valid(b))return 4;
    for(int i=offset;i+arm<192;i+=stride)for(int side:{0,1})
      arms.insert(canonical(b,i+side*arm,side?-1:1,arm));
  }
  Count pairs=0,perms=0;cerr<<"oriented forms "<<arms.size()<<" arm "<<arm<<"\n";
  for(auto a=arms.begin();a!=arms.end();++a){
    for(auto s=a;s!=arms.end();++s){
      vector<int>p(a->rbegin(),a->rend());p.insert(p.end(),s->begin()+1,s->end());
      Pivot t;++pairs;if(t.solve(p,arm)){
        for(int i=arm+1;i<=2*arm;i++)p[i]=t.mapped[p[i]];
        if(!valid(p))return 6;
        cout<<"FOUND ";for(int x:p)cout<<x<<" ";cout<<"\n";return 0;
      }
      if(t.leaves!=362880)return 7;perms+=t.leaves;
    }
  }
  cout<<"arm "<<arm<<" forms "<<arms.size()<<" pairs "<<pairs<<" perms "<<perms<<"\n";
}
