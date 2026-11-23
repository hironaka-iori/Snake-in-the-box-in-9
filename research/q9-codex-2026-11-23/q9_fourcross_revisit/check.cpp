#include <array>
#include <bitset>
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <set>
#include <string>
using namespace std;using M=bitset<256>;using P=vector<int>;
struct Arm{M body,block;};
M n[256];struct Check{
 P a,s;M A,S,basefixed;array<vector<Arm>,40> tail[2];set<pair<string,string>> found[2];long long visits=0,checks=0;int ng=0;
 void rec(int x,int len,M ban,M body,M block,int side){
  visits++;tail[side][len].push_back({body,block});if(len==39)return;
  for(int j=0;j<8;j++){int y=x^1<<j;if(ban[y])continue;auto b=body;b.set(y);auto f=ban|n[x];f.set(y);auto c=block|n[y];c.set(y);rec(y,len+1,f,b,c,side);}}
 void each(){ng++;S={};for(int x:s)S.set(x);
  for(int side=0;side<2;side++){for(auto&z:tail[side])z.clear();int root=side?a.back():a.front();M ban=A|S;
   for(int v:a)if(v!=root)ban|=n[v];for(int v:s)ban|=n[v];rec(root,0,ban,{}, {},side);}
  for(int ext:{38,39})for(int i=0;i<=ext;i++)for(auto&l:tail[0][i])for(auto&r:tail[1][ext-i]){
     checks++;if((l.block&r.body).any())continue;auto m=A|l.body|r.body;found[ext-38].insert({m.to_string(),S.to_string()});}
 }
};
int main(){for(int v=0;v<256;v++)for(int j=0;j<8;j++)n[v].set(v^1<<j);ifstream f("inputs.dat");int sid,na;f>>sid>>na;Check t;t.a.resize(na);if(na!=55)abort();M free;free.set();for(int&v:t.a){f>>v;t.A.set(v);free.reset(v);free&=~n[v];}
 for(int a=0;a<256;a++)if(free[a])for(int b=0;b<256;b++)if(free[b]&&n[a][b])for(int c=0;c<256;c++)if(free[c]&&c!=a&&n[b][c])
 for(int d=a+1;d<256;d++)if(free[d]&&d!=b&&n[c][d]&&!n[a][d]){t.s={a,b,c,d};t.each();}
 ofstream out("independent_sets.txt");for(int i=0;i<2;i++)for(auto&[m,s]:t.found[i])out<<92+i<<" "<<m<<" "<<s<<"\n";
 cout<<"shorts "<<t.ng<<" single_arm_nodes "<<t.visits<<" joins_tested "<<t.checks<<" L92 "<<t.found[0].size()<<" L93 "<<t.found[1].size()<<endl;}
