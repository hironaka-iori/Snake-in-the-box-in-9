#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
using namespace std;
bool valid(const vector<int>&w){array<bool,1024> used{};int cur=0;used[0]=true;for(int d:w){cur^=1<<d;if(used[cur])return false;int n=0;for(int k=0;k<10;k++)n+=used[cur^(1<<k)];if(n!=1)return false;used[cur]=true;}return true;}
int main(int argc,char**argv){ifstream f(argv[1]);ofstream dst(argv[2]),meta(argv[3]);mt19937 rng(721733);int id=0;string line;while(id<24&&getline(f,line)){istringstream in(line);vector<int>p,w;int x;while(in>>x)p.push_back(x);for(int j=1;j<p.size();j++)w.push_back(countr_zero(unsigned(p[j]^p[j-1])));
 bool done=false;for(int t=0;t<180000&&!done;t++){
 vector<int> axes{0,1,2,3,4,5,6,7,8};shuffle(axes.begin(),axes.end(),rng);vector<int> q=w;vector<int>pars;
 bool good=true;for(int j=0;j<3;j++){int a=axes[j],beg=j*64,end=min(191,beg+64);vector<int>pos;for(int k=beg;k<end;k++)if(w[k]==a)pos.push_back(k);if(pos.size()<3){good=false;break;}
 int i=rng()%(pos.size()-1);q[pos[i]]=q[pos[i+1]]=9;int u=-1,v=-1;
 if(j==1&&t%2==0){u=rng()%9;v=rng()%9;if(u==v)v=(v+1)%9;for(int k=beg;k<end;k++){if(q[k]==u)q[k]=v;else if(q[k]==v)q[k]=u;}}
 pars.insert(pars.end(),{a,pos[i],pos[i+1],u,v});}
 if(!good||!valid(q))continue;int successes=0;for(int a=1;a<10&&!successes;a++)for(int b=0;b<a&&!successes;b++){auto s=q;for(auto&d:s)if(d==a)d=b;successes+=valid(s);}
 if(successes)continue;dst<<"10 0";int v=0;for(int d:q){v^=1<<d;dst<<" "<<v;}dst<<endl;meta<<id<<" "<<t;for(int x:pars)meta<<" "<<x;meta<<endl;done=true;
 }if(!done)return 1;id++;}return 0;}
