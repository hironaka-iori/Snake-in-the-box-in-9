// Rebuild one entire parity class, including its ordering, after replacing
// any one vertex in the other parity class of a damaged target-length walk.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <set>
#include <sstream>
int main(int argc,char**argv){
 if(argc<2||argc>3)return 2;bool two=argc==3;
 uint64_t pairs=0,tests=0,low=0,dead=0,unknown=0;int seeds=0,sets=0;
 set<vector<int>> seen;
 string line;
 while(getline(cin,line)){
  istringstream in(line);vector<int>p;int x;while(in>>x)p.push_back(x);
  if(p.size()%2!=1)return 3;
  int left=-1,right=-1;
  if(two){for(int i=0;i<(int)p.size();i++)for(int j=i+2;j<(int)p.size();j++)if(__builtin_popcount(p[i]^p[j])==1){if(left!=-1)return 4;left=i;right=j;}
  if(left<0)return 5;}
  for(int side=0;side<2;side++){
   vector<int>a;for(int i=side;i<(int)p.size();i+=2)a.push_back(p[i]);
   sort(a.begin(),a.end());auto key=a;int hit=-1;
   if(two){hit=p[(left%2==side)?left:right];key.push_back(hit);}
   if(!seen.insert(key).second)continue;sets++;
   Search s(a,atoi(argv[1]),side==0);
   if(s.test())return 0;
   vector<int> extra;for(int v=0;v<512;v++)if(s.slot[v]<0&&!(__builtin_popcount(v^a[0])%2))extra.push_back(v);
   for(int i=0;i<(int)a.size();i++){
    if(two&&a[i]!=hit)continue;
    s.toggle(a[i],i,false);
    if(two){
     for(int j=0;j<(int)a.size();j++)if(j!=i){
      s.toggle(a[j],j,false);pairs++;
      vector<int>inside;
      for(int v:extra){
       int possible=0;for(int d=0;d<9;d++)possible+=__builtin_popcount((unsigned)s.axes[v^(1<<d)])<=1;
       if(possible>=(side==0?1:2))inside.push_back(v);
      }
      for(size_t u=0;u<inside.size();u++){
       s.fixed[i]=inside[u];s.toggle(inside[u],i,true);
       for(size_t k=0;k<u;k++){
        s.fixed[j]=inside[k];s.toggle(inside[k],j,true);if(s.test())return 0;s.toggle(inside[k],j,false);
       }
       s.toggle(inside[u],i,false);
      }
      s.fixed[j]=a[j];s.toggle(a[j],j,true);
     }
    }else for(int v:extra){
     s.fixed[i]=v;s.toggle(v,i,true);if(s.test())return 0;s.toggle(v,i,false);
    }
    s.fixed[i]=a[i];s.toggle(a[i],i,true);
   }
   tests+=s.tested;low+=s.low;dead+=s.dead;unknown+=s.unknown;
  }
  seeds++;
 }
 cout<<"DONE seeds "<<seeds<<" removal_pairs "<<pairs<<" parity_sets "<<sets<<" tests "<<tests<<" low "<<low<<" exhausted "<<dead<<" unknown "<<unknown<<endl;
}
