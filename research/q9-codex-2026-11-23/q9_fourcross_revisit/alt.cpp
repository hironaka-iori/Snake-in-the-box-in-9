#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;using P=vector<int>;using Key=array<uint64_t,4>;
struct Search{
 int source,L=92;long long cap,nodes=0,leftnodes=0,solutions=0;bool stopped=false;array<int,256>used{},nearby{};P anchor,small,a,b;Key bits{};set<Key>sets;ofstream out;
 Search(string f):out(f){}
 void mark(int v,int d,bool main){used[v]+=d;for(int i=0;i<8;i++)nearby[v^(1<<i)]+=d;if(main)bits[v>>6]^=1ULL<<(v&63);}
 void grow(bool left,int depth){if(stopped)return;if(nodes==cap){stopped=true;return;}nodes++;leftnodes+=left;
 if(depth==L){solutions++;if(sets.insert(bits).second){P path(a.rbegin(),a.rend());path.insert(path.end(),anchor.begin(),anchor.end());path.insert(path.end(),b.begin(),b.end());out<<source<<" 0 0 0 "<<path.size();for(int v:path)out<<" "<<v;out<<" "<<small.size();for(int v:small)out<<" "<<v;out<<endl;}return;}
 if(left)grow(false,depth);P&side=left?a:b;int tip=side.empty()?(left?anchor[0]:anchor.back()):side.back();for(int j=0;j<8&&!stopped;j++){int v=tip^(1<<j);if(used[v]||nearby[v]!=1)continue;side.push_back(v);mark(v,1,true);grow(left,depth+1);mark(v,-1,true);side.pop_back();}}
};
int main(int argc,char**v){if(argc!=4&&argc!=6)return 1;ifstream in("alt_inputs.dat");int id,n,k;while(in>>id>>n){P p(n);for(int&x:p)in>>x;in>>k;P q(k);for(int&x:q)in>>x;if(id>=atoi(v[1]))break;if(argc==6){int a=atoi(v[4]),b=atoi(v[5]);p=P(p.begin()+a,p.end()-b);}Search s(string(v[3])+"_"+to_string(id)+".dat");s.L=getenv("GOAL")?atoi(getenv("GOAL")):92;s.cap=atoll(v[2]);s.source=id;s.small=q;s.anchor=p;for(int x:p)s.mark(x,1,true);for(int x:q)s.mark(x,1,false);s.grow(true,p.size()-1);cout<<"source "<<id<<" cap "<<s.cap<<" nodes "<<s.nodes<<" left "<<s.leftnodes<<" routes "<<s.solutions<<" distinct "<<s.sets.size()<<" complete "<<!s.stopped<<endl;}}
