#include "q9_seed_growth.hpp"
#include <iostream>
#include <sstream>
#include <string>
using namespace std;
using Path=vector<int>;
Path ordered(Path set){
 auto adjacent=[](int x,int y){return has_single_bit(unsigned(x^y));};
 int end=-1;
 for(int x:set){
   int degree=count_if(set.begin(),set.end(),[&](int y){return adjacent(x,y);});
   if(degree>2||degree<1)abort();if(degree==1)end=x;
 }
 if(end<0)abort();
 Path p{end};
 while(p.size()<set.size()){
    int x=-1;for(int y:set)if(adjacent(y,p.back())&&(p.size()==1||y!=p[p.size()-2])){x=y;break;}
    if(x<0||find(p.begin(),p.end(),x)!=p.end())abort();p.push_back(x);
 }
 return p;
}
int main(int argc,char**argv){
 if(argc!=3)return 2;int g=stoi(argv[1]),e=stoi(argv[2]),rows=0;
 string l;while(getline(cin,l)){
    istringstream s(l);int x;Path a,b;while(s>>x)(x<256?a:b).push_back(x);
    SeedGrow solver;bool found=solver.run(ordered(a),ordered(b),9,g,e);
    if(found){
       const Path& p=solver.witness;for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)if(p[i]==p[j]||has_single_bit(unsigned(p[i]^p[j]))!=(j+1==i))abort();
       cout<<"FOUND "<<p.size()-1;for(int x:p)cout<<" "<<x;cout<<endl;return 0;
    }
    cout<<"NEG "<<rows++<<" "<<e<<" "<<solver.nodes<<endl;
 }cout<<"DONE "<<g<<" "<<e<<" "<<rows<<endl;
}
