#define BARRIER_LIBRARY
#include "barrier.cpp"
int main(){ifstream in("../q9_far189_spring_20261121/comparison191.words");string w;in>>w;
 string core=canonical(w.substr(12,w.size()-24));EndSearch search;search.run(core,0);
 string pw;for(int i=1;i<(int)search.bestpath.size();i++)pw+=char('0'+countr_zero(unsigned(search.bestpath[i]^search.bestpath[i-1])));
 cout<<search.best<<" "<<core<<" "<<pw<<endl;
 if(search.best<191)return 1;
}
