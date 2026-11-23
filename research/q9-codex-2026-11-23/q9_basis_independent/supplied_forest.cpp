// Execute just the supplied connectivity/completion routine on a batch of fixed bases.
#define main ignored_main
#include "../q9_change_basis/find.cpp"
#undef main
#include "../q9_change_basis/forest.hpp"
int main(){string line;int row=0;while(getline(cin,line)){
 istringstream f(line);int h,x;f>>h;Bits set;while(f>>x)set.set(x);vector<int> output;
 bool r=grow(set,h,output);cout<<row++<<" "<<r;for(int v:output)cout<<" "<<v;cout<<endl;
}}
