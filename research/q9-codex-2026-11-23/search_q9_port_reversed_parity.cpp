// When endpoints have opposite color to those of a near walk, try retaining
// an entire parity class except for the one vertex required by its new size.
#define Q9_PARITY_LIBRARY
#include "search_q9_fixed_parity.cpp"
#include <set>
#include <sstream>
int main(int argc,char**){
 string l;set<vector<int>> seen;uint64_t tests=0,bound=0,dead=0,unknown=0;
 while(getline(cin,l)){vector<int>p;istringstream in(l);int x;while(in>>x)p.push_back(x);
 for(int side=0;side<2;side++){vector<int>a;
 for(int i=side;i<(int)p.size();i+=2)a.push_back(p[i]);
 sort(a.begin(),a.end());if(!seen.insert(a).second)continue;
 if(argc>1){
 if(side)continue;
 // Convert 97 to 96 while also changing one vertex of the new minority.
 for(size_t i=0;i<a.size();i++)for(size_t j=0;j<i;j++){
 vector<int>b;for(size_t k=0;k<a.size();k++)if(k!=i&&k!=j)b.push_back(a[k]);
 Search s(b,40000,false);
 bool possible=true;for(int z:b){int room=0;for(int d=0;d<9;d++)room+=__builtin_popcount(unsigned(s.axes[z^(1<<d)]))<=2;
 if(room<2){possible=false;break;}}
 if(!possible)continue;
 s.fixed.push_back(-1);int k=b.size();
 for(int u=0;u<512;u++)if(!(__builtin_popcount(u^a[0])%2)&&!binary_search(a.begin(),a.end(),u)){
 int room=0;for(int d=0;d<9;d++)room+=__builtin_popcount(unsigned(s.axes[u^(1<<d)]))<=1;
 if(room<2)continue;
 s.toggle(u,k,true);s.fixed[k]=u;if(s.test())return 0;s.toggle(u,k,false);
 }
 tests+=s.tested;bound+=s.low;dead+=s.dead;unknown+=s.unknown;
 }
 }else if(!side){ // 97 to 96: remove one; endpoints in the opposite parity.
 for(int u:a){auto b=a;b.erase(find(b.begin(),b.end(),u));Search s(b,40000,false);if(s.test())return 0;tests++;bound+=s.low;dead+=s.dead;unknown+=s.unknown;}
 }else{ // 96 to 97: add one; endpoints in this parity.
 for(int u=0;u<512;u++)if(!(__builtin_popcount(u^a[0])%2)&&!binary_search(a.begin(),a.end(),u)){auto b=a;b.push_back(u);Search s(b,40000,true);if(s.test())return 0;tests++;bound+=s.low;dead+=s.dead;unknown+=s.unknown;}
 }}}
 cout<<"DONE source_sets "<<seen.size()<<" tests "<<tests<<" low "<<bound<<" exhausted "<<dead<<" unknown "<<unknown<<endl;
}
