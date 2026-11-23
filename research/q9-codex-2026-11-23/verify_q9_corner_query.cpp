#define Q9_CORNER_DRIVER
#include "search_q9_corners_and_tips.cpp"
int main(){string line;while(getline(cin,line)){
    istringstream in(line);int id,split,gap,l,r;in>>id>>split>>gap>>l>>r;int x;Path p;
    while(in>>x)p.push_back(x);
    Engine e(p,0,split);
    bool ok=split<0?e.visit(l,r,Forced{}):e.connect(gap,l,r,Forced{});
    cout<<id<<" "<<ok<<" "<<e.nodes;
    for(int v:e.witness)cout<<" "<<v;cout<<endl;
}}
