#define main unused_extract_main
#include "extract.cpp"
#undef main
#include <set>
int main(int argc,char**argv){int nmin=stoi(argv[1]);set<Bits> seen;map<Bits,array<int,4>>saved;long long tested=0,good=0,invalid=0;int row=0;string w;
while(cin>>w){vector<int>p{0};for(char c:w)p.push_back(p.back()^1<<(c-'0'));
 for(int d=0;d<9;d++)for(int s=0;s<2;s++){Bits b{};vector<int>vs;
  for(int v:p)if(((v>>d)&1)==s){int x=(v&((1<<d)-1))|((v>>(d+1))<<d);put(b,x);vs.push_back(x);}
  if(vs.size()<nmin||!seen.insert(b).second)continue;Forest initial;if(get(b,initial))continue;invalid++;
  vector<int> bad;for(int x:vs){int deg=0;for(int j=0;j<8;j++)deg+=has(b,x^1<<j);if(deg>=3)bad.push_back(x);}
  for(int x:vs){bool possible=true;for(int y:bad)if(x!=y&&popcount(unsigned(x^y))!=1){possible=false;break;}if(!possible)continue;
   tested++;auto a=b;a[x/64]^=1ull<<(x%64);Forest f;if(!get(a,f))continue;good++;auto z=canonical(f);saved.try_emplace(z,array<int,4>{row,d,s,x});
  }
 }row++;}
 cout<<"META "<<row<<" "<<invalid<<" "<<tested<<" "<<good<<" "<<saved.size()<<endl;
 for(auto&[m,z]:saved){cout<<"F";for(int x:z)cout<<" "<<x;for(auto x:m)cout<<" "<<x;cout<<'\n';}
}
