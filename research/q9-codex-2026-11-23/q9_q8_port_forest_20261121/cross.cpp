#define Q8_CROSS_DRIVER
#include "match.cpp"
set<Bits> readbanks(int begin,int end,char**argv){
 set<Bits> out;for(int i=begin;i<end;i++){ifstream in(argv[i]);string l;while(getline(in,l)){istringstream ss(l);string t;ss>>t;if(t!="F")continue;int x;for(int j=0;j<4;j++)ss>>x;Bits b{};for(auto&v:b)ss>>v;out.insert(b);}}return out;
}
int main(int argc,char**argv){
 auto base=readbanks(1,3,argv),edit=readbanks(3,argc,argv);for(auto b:base)bank.emplace_back(b);
 for(auto b:edit)bank.emplace_back(b);Solver s{};s.minGoal=192;s.exact=false;
 bool ok=s.run(base.size());auto c=s.c;cout<<"DONE "<<base.size()<<" "<<edit.size()<<" "<<ok<<" "<<c.probes<<" "<<c.hits<<" "<<c.maps<<" "<<c.portmaps<<" "<<c.legalOverlap<<" "<<c.cycles<<endl;
}
