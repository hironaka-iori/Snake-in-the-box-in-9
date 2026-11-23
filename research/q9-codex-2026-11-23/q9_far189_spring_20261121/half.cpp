#define main unused_parity_driver
#include "../search_q9_parity_combinations.cpp"
#undef main
#include <set>
int main(int argc,char**argv){
 int drops=stoi(argv[1]),row=0;string w;set<vector<int>> seen;long long removals=0,addnodes=0,qualified=0;
 while(cin>>w){vector<int>p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
  if(p.size()!=190)return 3;
  for(int side=0;side<2;side++){
   vector<int>s,pool;for(int i=side;i<p.size();i+=2)s.push_back(p[i]);
   Bounds bounds;for(int v:s)bounds.change(v,1);
   for(int v=0;v<512;v++)if(!bounds.occupied[v]&&!__builtin_parity(unsigned(s[0]^v)))pool.push_back(v);
   auto add=[&](auto&&self,const vector<int>&opt,int st,int need)->void{
    if(need==0){if(bounds.counts[2]<95)return;qualified++;
      vector<int> pts;for(int v=0;v<512;v++)if(bounds.occupied[v])pts.push_back(v);if(pts.size()!=96)abort();
      if(seen.insert(pts).second){cout<<"HALF "<<row<<" "<<side;for(int v:pts)cout<<" "<<v;cout<<'\n';}return;}
    for(int i=st;i+need<=opt.size();i++){int v=opt[i];if(bounds.room[v]==0)continue;
      bounds.change(v,1);addnodes++;if(bounds.poor<=2)self(self,opt,i+1,need-1);bounds.change(v,-1);}
   };
   auto del=[&](auto&&self,int st,int need)->void{
    if(!need){removals++;if(bounds.poor>2)return;
     vector<int> viable;for(int x:pool){bounds.change(x,1);if(bounds.poor<=2&&bounds.room[x]>0)viable.push_back(x);bounds.change(x,-1);}
     add(add,viable,0,drops+1);return;}
    for(int i=st;i+need<=s.size();i++){bounds.change(s[i],-1);self(self,i+1,need-1);bounds.change(s[i],1);}
   };del(del,0,drops);
  }
  row++;
 }cout<<"DONE "<<row<<" "<<removals<<" "<<addnodes<<" "<<qualified<<" "<<seen.size()<<endl;
}
