// At every split strictly between the unique chord ends, try the entire S9
// point stabilizer on one side. The two outside split regions retain the chord.
#define main pivot_original_driver
#include "search_q9_pivot.cpp"
#undef main
#include <sstream>
int main(){
 string line;Count seeds=0,domains=0,permutations=0,nodes=0;
 while(getline(cin,line)){
  istringstream in(line);vector<int>p;int x;
  while(in>>x){if(x<0||x>511)return 2;p.push_back(x);}if(p.empty())continue;
  int a=-1,b=-1,hits=0;
  for(int i=0;i<(int)p.size();i++)for(int j=i+1;j<(int)p.size();j++){
   int h=popcount((unsigned)(p[i]^p[j]));
   if(!h||(j==i+1&&h!=1))return 3;
   if(j>i+1&&h==1){a=i;b=j;hits++;}
  }
  if(hits!=1)return 4;
  for(int k=a+1;k<b;k++){
   Pivot engine;
   if(engine.solve(p,k)){
    auto q=p;for(int j=k+1;j<(int)q.size();j++)q[j]=p[k]^engine.mapped[p[j]^p[k]];
    if(!valid(q))return 5;
    cout<<"FOUND "<<seeds<<" "<<k;for(int v:q)cout<<" "<<v;cout<<endl;return 0;
   }
   if(engine.leaves!=362880)return 6;
   permutations+=engine.leaves;nodes+=engine.nodes;domains++;
  }
  if(++seeds%100==0)cout<<"CHECK "<<seeds<<" cuts "<<domains<<" permutations "<<permutations<<" nodes "<<nodes<<endl;
 }
 cout<<"DONE "<<seeds<<" cuts "<<domains<<" permutations "<<permutations<<" nodes "<<nodes<<endl;
}
