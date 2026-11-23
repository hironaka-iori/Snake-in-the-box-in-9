// Generate induced, rooted arms by independently recoloring distant transitions.
#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Word=vector<int>;
string norm(const Word&w){array<int,9> lab{};string s;int k=0;for(int d:w){if(!lab[d])lab[d]=++k;s+=char('0'+lab[d]-1);}return s;}
bool decode(const Word&w,vector<int>&p){
 array<unsigned char,512> touch{};bitset<512>used;int v=0;
 p={0};used.set(0);for(int d=0;d<9;d++)touch[1<<d]=1;
 for(int d:w){v^=1<<d;if(used[v]||touch[v]!=1)return false;
 used.set(v);p.push_back(v);for(int i=0;i<9;i++)touch[v^(1<<i)]++;}
 return true;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;const int len=stoi(argv[1]),rounds=stoi(argv[2]),limit=stoi(argv[3]);mt19937 rng(stoul(argv[4]));
 set<string> existing,out;vector<Word> bank;vector<int>p;string l;
 while(getline(cin,l)){istringstream in(l);int x;vector<int>path;while(in>>x)path.push_back(x);
 for(int dir=0;dir<2;dir++,reverse(path.begin(),path.end()))
 for(int start=0;start+len<(int)path.size();start+=6){Word w;bool ok=true;
 for(int t=start;t<start+len;t++){int d=path[t]^path[t+1];if(__builtin_popcount(unsigned(d))!=1){ok=false;break;}w.push_back(__builtin_ctz(unsigned(d)));}
 if(ok&&decode(w,p)&&existing.insert(norm(w)).second)bank.push_back(std::move(w));
 }}
 if(bank.empty())return 3;size_t original=bank.size();long long proposed=0,valid=0;
 for(int k=0;k<rounds&&(int)out.size()<limit;k++){auto w=bank[rng()%bank.size()];int n=1+rng()%3;
 for(int j=0;j<n;j++){int i=rng()%len;w[i]=(w[i]+1+rng()%8)%9;}proposed++;
 if(!decode(w,p))continue;valid++;auto key=norm(w);
 if(existing.count(key)||!out.insert(key).second)continue;
 if(rng()%2==0)bank.push_back(w);
 for(int v:p)cout<<v<<" ";cout<<"\n";
 }
 cerr<<"original "<<original<<" proposed "<<proposed<<" valid "<<valid<<" new_rooted "<<out.size()<<endl;
}
