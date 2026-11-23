// Search previously unseen arms obtained by rerouting one corner of a 96-edge arm.
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
  const int len=96,stride=argc>1?atoi(argv[1]):24;set<vector<int>> all,sample,fresh;
  vector<int>b(192);
  while(cin>>b[0]){
    for(int i=1;i<192;i++)if(!(cin>>b[i]))return 3;
    if(!valid(b))return 4;
    for(int i=0;i+len<192;i++)for(int side:{0,1}){
      auto arm=canonical(b,i+side*len,side?-1:1,len);
      all.insert(arm);if(i%stride==0)sample.insert(arm);
    }
  }
  for(const auto&arm:sample)for(int j=1;j<len;j++){
    auto v=arm;v[j]=v[j-1]^v[j]^v[j+1];if(!valid(v))continue;
    auto key=canonical(v,0,1,len);if(!all.count(key))fresh.insert(key);
  }
  cerr<<"known "<<all.size()<<" sample "<<sample.size()<<" novel "<<fresh.size()<<"\n";
  Count pairs=0;
  for(auto s=fresh.begin();s!=fresh.end();++s){
    auto check=[&](const vector<int>&a){
      vector<int>p(a.rbegin(),a.rend());p.insert(p.end(),s->begin()+1,s->end());++pairs;
      Pivot t;if(!t.solve(p,len))return t.leaves==362880?0:7;
      for(int i=len+1;i<=2*len;i++)p[i]=t.mapped[p[i]];
      if(!valid(p))return 6;
      cout<<"FOUND ";for(int x:p)cout<<x<<" ";cout<<"\n";return 1;
    };
    for(const auto&a:all){int ret=check(a);if(ret)return ret==1?0:ret;}
    for(auto a=s;a!=fresh.end();++a){int ret=check(*a);if(ret)return ret==1?0:ret;}
  }
  cout<<"pairs "<<pairs<<" no valid join\n";return 0;
}
