#include "direct_fill.hpp"
struct CachedFill {
    vector<int> basis,tips;array<int,512> inverse;DirectFill f;
    bool solve(const vector<int>&g,const vector<int>&p,const vector<int>&rm,int target,int tag){
      if(g!=basis){basis=g;f=DirectFill();f.goal=target;tips.clear();
        for(int i=0;i<512;i++){int v=0;for(int a=0;a<9;a++)if(i&(1<<a))v^=g[a];inverse[v]=i;}
        for(int v:p)f.toggle(inverse[v],true);
        for(int v:p){int x=inverse[v];if(f.degrees[x]<2)tips.push_back(x);}
      }
      f.trail=tips;for(int v:rm)f.toggle(inverse[v],false);
      for(int v:rm){int x=inverse[v];for(int a=0;a<9;a++){int y=x^(1<<a);if(f.occupied[y]&&f.degrees[y]<2)f.trail.push_back(y);}}
      bool yes=f.append(target+1-p.size()+rm.size());for(int v:rm)f.toggle(inverse[v],true);
      if(yes){cout<<"FOUND "<<tag<<" locked -1 basis";for(int v:g)cout<<' '<<v;cout<<" path";for(int v:f.answer)cout<<' '<<v;cout<<endl;}return yes;
    }
};
