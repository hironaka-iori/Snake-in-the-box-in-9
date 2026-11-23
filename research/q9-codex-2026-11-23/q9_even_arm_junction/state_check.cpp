#define Q9_FLEX_LIBRARY
#include "../q9_tree_lifts/flexible.cpp"
#include <sstream>
#include <fstream>
using U=uint64_t;
U prefixes=0,choices=0,accept=0;
void compare(const State&s){
 array<unsigned short,512> cnt{};array<bool,512> selected{};vector<array<int,2>> port;
 for(int i=0;i<=s.k;i++){int v=s.seq[i];assert(!selected[v]);selected[v]=true;for(int b=1;b<512;b*=2)cnt[v^b]++;}
 for(int i=1;i<=s.k;i++){int a=s.seq[i-1],b=s.seq[i],m=a^b,lsb=m&-m;assert(popcount(unsigned(m))==2);port.push_back({a^lsb,b^lsb});}
 for(int p=0;p<9;p++)for(int q=0;q<p;q++){
 int a=1<<p,b=1<<q,x=s.v^a^b;bool yes=!selected[x]&&(cnt[s.v^a]==1||cnt[s.v^b]==1);
 if(yes)for(auto ends:port){bool ok=false;for(int o:ends)ok|=(cnt[o]+int(popcount(unsigned(o^x))==1)==2);if(!ok){yes=false;break;}}
 assert(yes==s.possible(a,b));choices++;accept+=yes;}
 prefixes++;}
int main(int argc,char**argv){ifstream f(argv[1]);string ln;int rows=0;while(getline(f,ln)){istringstream in(ln);P ms;int v;while(in>>v)ms.push_back(v);assert(ms.size()==48);
 for(int side=0;side<2;side++){if(side)reverse(ms.begin(),ms.end());State s;compare(s);for(int m:ms){s.push(m&-m,m^(m&-m));compare(s);}}rows++;}
 cout<<"DONE arms "<<rows<<" oriented_prefixes "<<prefixes<<" compared_choices "<<choices<<" accepted "<<accept<<endl;}
