#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <string>
#include <vector>
using namespace std;
struct Mother {string word;int a,b;};
vector<Mother> mothers;
void read_mothers(const char*path){ifstream in(path);Mother x;while(in>>x.word>>x.a>>x.b)mothers.push_back(x);}
struct Layout {
 array<bool,256> low{},port{},pool{};
 int m=0,delta=0,nlow=0,upper_ends=0;
 Layout(int i,int code) {
  const auto &g=mothers.at(i);assert(code>=0&&code<4&&g.word.size()==93);int q=0;
  low[q]=true;for(char c:g.word){q^=1<<(c-'0');assert(!low[q]);low[q]=true;}
  assert(popcount(unsigned(g.a^g.b))==1);
  for(int x=0;x<256;x++)if(low[x])assert(popcount(unsigned(x^g.a))>=2&&popcount(unsigned(x^g.b))>=2);
  int y=code<2?g.a:g.b,z=code<2?g.b:g.a;low[y]=low[z]=port[y]=true;
  m=popcount(unsigned(z))%2;upper_ends=code%2;
  if(upper_ends)port[0]=port[q]=true;
  else port[m==0?q:0]=true;
  for(int x=0;x<256;x++){pool[x]=!low[x]||port[x];if(low[x]){nlow++;delta+=1-2*(popcount(unsigned(x))%2);}}
  delta-=1-2*m;
 }
};
