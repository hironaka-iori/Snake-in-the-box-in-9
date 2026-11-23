#define main unused_extract_main
#include "extract.cpp"
#undef main
#include <fstream>
#include <sstream>
#include <set>
int main(int argc,char**argv){
 int drops=stoi(argv[1]),nmin=stoi(argv[2]),nmax=stoi(argv[3]),cap=stoi(argv[4]);set<Bits> all;for(int i=5;i<argc;i++){
 ifstream in(argv[i]);string line;while(getline(in,line)){istringstream ss(line);string t;ss>>t;if(t!="F")continue;int x;for(int j=0;j<4;j++)ss>>x;Bits b{};for(auto&z:b)ss>>z;all.insert(b);}}
 map<Bits,array<int,3>> shapes;long long tries=0,safe=0;int sources=0,id=-1;
 for(Bits b:all){id++;Forest f;if(!get(b,f))abort();int n=f.vs.size();if(n<nmin||n>nmax||sources>=cap)continue;sources++;
   auto test=[&](int x,int y){Bits m=b;m[x/64]^=1ull<<(x%64);if(y>=0)m[y/64]^=1ull<<(y%64);
    tries++;Forest g;if(!get(m,g))return;safe++;Bits k=canonical(g);shapes.try_emplace(k,array<int,3>{id,x,y});};
   for(int i=0;i<n;i++){int x=f.vs[i];if(drops==1)test(x,-1);else for(int j=0;j<i;j++)test(x,f.vs[j]);}
 }
 cout<<"META "<<sources<<" "<<tries<<" "<<safe<<" "<<shapes.size()<<endl;
 for(auto&[b,s]:shapes){cout<<"F "<<drops<<" "<<s[0]<<" "<<s[1]<<" "<<s[2];for(unsigned long long z:b)cout<<" "<<z;cout<<'\n';}
}
