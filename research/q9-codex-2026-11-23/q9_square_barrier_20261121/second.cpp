#define BARRIER_LIBRARY
#include "barrier.cpp"
#include <sstream>
int main(int argc,char**argv){
 if(argc!=7)return 2;
 Experiment ex(stoi(argv[1]),stoi(argv[2]),stoi(argv[3]),stoi(argv[4]),argv[6]);ex.roots.clear();
 ifstream input(argv[5]);string line;
 while(getline(input,line)){istringstream ss(line);string orig,w;ss>>orig>>w;auto it=ex.closure.insert(w);if(it.second)ex.roots.push_back(&*it.first);}
 for(size_t i=0;i<ex.roots.size();i++){const string& w=*ex.roots[i];Middle s(w);
  for(int j=1;j+1<int(s.p.size());j++){int x=s.alt(j);if(s.ix[x]>=0||s.adj[x]!=2)continue;
   string a=w;swap(a[j-1],a[j]);auto it=ex.closure.insert(canonical(a));if(it.second)ex.roots.push_back(&*it.first);
  }
 }
 cout<<"OUTER_CLOSURE "<<ex.roots.size()<<" cumulative "<<ex.closure.size()<<endl;
 shuffle(ex.roots.begin(),ex.roots.end(),ex.gen);ex.run();
}
