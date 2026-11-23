#define Q9_PARITY_LIBRARY
#include "../search_q9_fixed_parity.cpp"
#include <sstream>
struct Sink:streambuf{int overflow(int c)override{return c;}};
int main(){string l;Sink sink;auto*orig=cout.rdbuf();int total=0,pass=0,unknown=0,lows=0,dead=0;
 while(getline(cin,l)){istringstream s(l);string tag;int i,j;s>>tag;if(tag!="HALF")continue;s>>i>>j;vector<int>p;int v;while(s>>v)p.push_back(v);
  Search h(p,100000,true);cout.rdbuf(&sink);bool ok=h.test();cout.rdbuf(orig);total++;unknown+=h.unknown;lows+=h.low;dead+=h.dead;
  if(ok||h.unknown){pass++;cout<<l<<'\n';}
 }
 cout<<"DONE "<<total<<" "<<pass<<" "<<lows<<" "<<dead<<" "<<unknown<<endl;
}
