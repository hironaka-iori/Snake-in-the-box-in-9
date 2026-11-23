#define PORT_GRAPH_LIBRARY
#include "port_graph.cpp"
int main(int argc,char**argv){ifstream in(argv[1]);string line;int id=0;rankOf={0};while(getline(in,line)){int n,m;istringstream f(line);f>>n>>m;P a(n),b(m);for(auto&v:a)f>>v;for(auto&v:b)f>>v;trie.clear();trie.resize(1);put(b,0);won=false;Join j(a,id++,0,10000000,true);j.dfs(0,0);assert(won);}
 cout<<"DONE "<<id<<" "<<nodes<<" "<<tests<<" "<<terms<<" "<<unknown<<endl;}
