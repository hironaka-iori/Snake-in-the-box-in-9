#define Q9_PARITY_LIBRARY
#include "../search_q9_fixed_parity.cpp"
#include <array>
#include <set>
#include <map>
#include <sstream>
using Set=array<uint64_t,4>;
int hw(int x){return popcount(unsigned(x));}
void toggle(Set&b,int x){b[x>>7]^=uint64_t(1)<<((x>>1)&63);}
bool has(const Set&b,int x){return b[x>>7]>>((x>>1)&63)&1;}
int decode(int q){return q*2+(hw(q)&1);}
bool oddLength(Search&s,int chosen,vector<int>&path){
 Graph g(s.fixed,s.cap);int n=s.fixed.size();
 g.add(chosen,g.dummy,-1);
 for(int v=0;v<512;v++){
  int m=s.axes[v],cnt=hw(m);if(cnt!=1&&cnt!=2)continue;int a=s.slot[v^(1<<countr_zero((unsigned)m))];m&=m-1;
  int b=m?s.slot[v^(1<<countr_zero((unsigned)m))]:g.dummy;
  g.add(a,b,v);
 }
 vector<int8_t> states(g.edges.size());states[0]=1;
 if(g.visit(states)!=1)return false;
 path=g.witness;return true;
}
bool verify(const vector<int>&p){
 for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||((hw(p[i]^p[j])==1)!=(i==j+1)))return false;
 return true;
}
int main(int argc,char**argv){
 int maxrows=atoi(argv[1]),goal=atoi(argv[2]),kind=atoi(argv[3]);
 const int minchanged=argc>4?atoi(argv[4]):3;
 int row=0;uint64_t proposals=0,moves=0,low=0,dead=0,unknown=0;map<int,int> hits;
 set<Set> survivors;
 string word;while(cin>>word&&row<maxrows){
  vector<int>p{0};for(char ch:word)p.push_back(p.back()^(1<<(ch-'0')));
  if(p.size()!=192||!verify(p))return 2;
  for(int side:{0,1}){
   Set a{};for(int i=side;i<p.size();i+=2)toggle(a,p[i]^side);
   for(int t=1;t<512;t++)if(hw(t)==2){
    vector<int>only;for(int q=0;q<256;q++){int x=decode(q);if(has(a,x)&&!has(a,x^t))only.push_back(x);}
    for(int c=0;c<512;c++)if(c<(c^t)){
     Set b=a;int swaps=0;
     for(int x:only){int d=min(hw(x^c),hw(x^c^t));bool include=kind==0?d<=2:kind==1?d==3:kind==2?d<=3:d==4;
      if(include){toggle(b,x);toggle(b,x^t);swaps++;}}
     proposals++;if(swaps<minchanged)continue;moves++;
     vector<int> fixed;
     for(int q=0;q<256;q++)if(has(b,decode(q)))fixed.push_back(decode(q));
     Search s(fixed,100000);
     if(goal==192){
      if(s.test()){cout<<"SOURCE "<<row<<" side "<<side<<" involution "<<t<<" center "<<c<<" swaps "<<swaps<<endl;return 0;}
      low+=s.low;dead+=s.dead;unknown+=s.unknown;if(!s.low){if(survivors.insert(b).second && argc>5){cout<<"CASE";for(int x:fixed)cout<<" "<<x;cout<<char(10);}hits[swaps]++;}
     }else{
      int weak=0;int forced=-1;for(int i=0;i<fixed.size();i++){int count=0;for(int k=0;k<9;k++)count+=hw(s.axes[fixed[i]^(1<<k)])<=2;
       if(count<2){weak++;forced=i;}if(count==0){weak=2;break;}}
      if(weak>1){low++;continue;}
      vector<int>w;for(int i=0;i<fixed.size();i++){if(forced>=0&&i!=forced)continue;if(!oddLength(s,i,w))continue;
       if(w.size()!=192||!verify(w))abort();cout<<"FOUND";for(int v:w)cout<<" "<<v;cout<<"\nSOURCE "<<row<<" side "<<side<<" involution "<<t<<" center "<<c<<" swaps "<<swaps<<endl;return 0;}
     }
    }
   }
  }row++;
 }
 cout<<"DONE rows "<<row<<" proposed "<<proposals<<" tested "<<moves<<" low "<<low<<" dead "<<dead<<" unknown "<<unknown<<" unique_graph_tests "<<survivors.size()<<" swaps_graph_tests";for(auto [k,v]:hits)cout<<" "<<k<<":"<<v;cout<<endl;
}
