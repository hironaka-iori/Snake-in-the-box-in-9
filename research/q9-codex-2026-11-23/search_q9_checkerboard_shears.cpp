// Preserve one Q8 checkerboard colour under invertible GF(2) shears,
// then search for a connected Q9 path by refilling the opposite colour.
#define main state_driver
#include "search_q9_checkerboard_states.cpp"
#undef main
#include <set>
int main(int argc,char**argv){
 if(argc!=3)return 2;int trials=stoi(argv[1]),budget=stoi(argv[2]);string line;
 while(getline(cin,line)){istringstream in(line);int id,c,z;in>>id>>c;vector<int>A;while(in>>z)A.push_back(z);
  std::mt19937 rng(881993+id);int complete=0,unknown=0;long long nodes=0;
  std::set<std::array<unsigned long long,8>> seen;
  for(int i=0;i<trials;i++){
   int bit1=rng()%8,bit2=(bit1+1+rng()%7)%8;
   int t=(1<<bit1)|(1<<bit2);if(rng()%3==0)t^=256;if(i%5==0)t=256;
   int mask=1+rng()%511;
   if(__builtin_parity(unsigned(t&mask)))mask^=t&-t;
   if(!mask||mask==t)continue;int off=rng()%2;
   std::array<unsigned long long,8> key{};vector<int> changed;
   for(int x:A){int y=x;if(__builtin_parity(unsigned(x&mask))^off)y^=t;changed.push_back(y);key[y/64]|=1ull<<(y%64);}
   if(!seen.insert(key).second)continue;int dist=0;for(int x:A)dist+=!(key[x/64]>>(x%64)&1);
   if(dist<4)continue;Check test(changed,c,192,budget);bool found=test.run(test.domain);nodes+=test.nodes;
   if(found){cout<<"FOUND "<<id<<" "<<t<<" "<<mask<<" "<<off;for(int v:test.witness)cout<<" "<<v;cout<<endl;return 0;}
   ++complete;if(test.capped){++unknown;cout<<"UNKNOWN "<<id<<" "<<t<<" "<<mask<<" "<<off<<"\n";}
  }
  cout<<"DONE "<<id<<" "<<complete<<" "<<unknown<<" "<<nodes<<endl;
 }
}
