#define BARRIER_LIBRARY
#include "barrier.cpp"
#include <sstream>
int main(int argc,char**argv){
 if(argc!=4)return 2;int cap=stoi(argv[1]);ifstream input(argv[2]);ofstream records(string(argv[3])+".records");
 unordered_set<string> seen;vector<const string*> q;string line;
 while(getline(input,line)){istringstream ss(line);string p,w;ss>>p>>w;if(w.empty())continue;if(seen.insert(w).second)q.push_back(&*seen.find(w));}
 size_t roots=q.size(),done=0, calls=0;int best=0;uint64_t nodes=0;
 mt19937 gen(721);shuffle(q.begin(),q.end(),gen);
 for(size_t a=0;a<q.size()&&done<(size_t)cap;a++){
  const string& p=*q[a];Middle s(p);
  for(int j=1;j+1<int(s.p.size());j++){
   int x=s.alt(j);if(s.ix[x]>=0||s.adj[x]!=2)continue;
   calls++;
   string w=p;swap(w[j-1],w[j]);w=canonical(w);auto ins=seen.insert(w);if(!ins.second)continue;
   q.push_back(&*ins.first);done++;
   EndSearch es;bool found=es.run(w,best);nodes+=es.nodes;
   if(es.best>best){
    best=es.best;string pw;for(int i=1;i<(int)es.bestpath.size();i++)pw+=char('0'+countr_zero(unsigned(es.bestpath[i]^es.bestpath[i-1])));
    records<<best<<" "<<w<<" "<<pw<<endl;cout<<"BEST "<<best<<" "<<done<<endl;
   }
   if(found){cout<<"FOUND 192"<<endl;return 0;}
   if(done>=(size_t)cap)break;
  }
 }
 cout<<"DONE seeds "<<roots<<" extra "<<done<<" legalmoves "<<calls<<" endnodes "<<nodes<<" best "<<best<<endl;
}
