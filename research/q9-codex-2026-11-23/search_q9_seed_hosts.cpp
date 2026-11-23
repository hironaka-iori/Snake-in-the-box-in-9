#include "q9_seed_growth.hpp"
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
using namespace std;
struct Placement{int a,b,t;string perm;};
int main(int argc,char**argv){
 if(argc!=4)return 2;int target=stoi(argv[1]),out=stoi(argv[2]),limit=stoi(argv[3]);
 vector<vector<int>> donors(753);string line;ifstream groups("q8_registered_donor_clusters.txt");if(!groups)return 2;
 while(getline(groups,line)){istringstream s(line);int g,id,x;s>>g>>id;while(s>>x)donors.at(id).push_back(x);}
 vector<Placement> records;
 while(getline(cin,line)){istringstream s(line);string k;s>>k;if(k!="HOST")continue;int a,b,t,c;string p;s>>a>>b>>t>>c>>p;records.push_back({a,b,t,p});}
 mt19937 rng(445712);shuffle(records.begin(),records.end(),rng);
 uint64_t total=0;int step=0;
 for(auto &r:records){
    vector<int> moved;for(int x:donors[r.b]){int y=r.t;for(int j=0;j<8;j++)if((x>>j)&1)y^=1<<(r.perm[j]-'0');moved.push_back(256+y);}
    SeedGrow solver;bool ok=solver.run(donors[r.a],moved,9,target,out);
    if(ok){auto &p=solver.witness;for(int i=0;i<p.size();i++)for(int j=0;j<i;j++)if(p[j]==p[i]||has_single_bit(unsigned(p[j]^p[i]))!=(j+1==i))abort();
      cout<<"FOUND "<<p.size()-1;for(int x:p)cout<<" "<<x;cout<<endl;return 0;}
    total+=solver.nodes;step++;
    if(step<5||step%100==0)cout<<"AT "<<step<<" "<<total<<endl;
    if(limit>0&&step==limit)break;
 }cout<<"DONE "<<target<<" "<<out<<" "<<step<<" "<<total<<endl;
}
