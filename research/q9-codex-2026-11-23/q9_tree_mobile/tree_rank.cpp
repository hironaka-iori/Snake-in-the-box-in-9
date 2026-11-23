#define Q9_TREE_LIBRARY
#include "../q9_tree_lifts/tree.cpp"
int main(){Edges e{};e[0]={0,1};e[1]={1,2};grow(e,3);int r,k;while(cin>>r>>k){cout<<r<<" "<<k;for(int x:trees[k].masks)cout<<" "<<x;cout<<"\n";}}
