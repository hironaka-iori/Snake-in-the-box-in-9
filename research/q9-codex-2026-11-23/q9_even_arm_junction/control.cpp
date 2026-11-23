#define main junction_driver
#include "junction.cpp"
#undef main
int main(int argc,char**argv){ifstream f(argv[1]);string l;control=1;limit=1000000000;image.fill(-1);while(getline(f,l)){istringstream ss(l);P a(48),b(47);for(int&x:a)ss>>x;for(int&x:b)ss>>x;trie.clear();trie.resize(1);insert(b,0);auto s=seed(a);hit=false;local=0;best=0;image.fill(-1);used=0;which=rows++;visit(s,0,0);assert(hit);}cout<<"DONE controls "<<rows<<" states "<<states<<" attempts "<<attempts<<endl;}
