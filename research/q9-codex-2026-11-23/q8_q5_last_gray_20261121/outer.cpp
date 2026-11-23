#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <unordered_map>
using namespace std;using U=uint32_t;
U N[32],masks[3];int goal,bounds[]={0,14,26,39};uint64_t visits[3],queries;unordered_map<U,int> memo;
int longest(int x,U m,U ban){int best=popcount(m);for(U s=N[x]&~(m|ban);s;s&=s-1){int y=countr_zero(s);best=max(best,longest(y,m|(U(1)<<y),ban|N[x]));}return best;}
int maximum(U allowed){
 auto it=memo.find(allowed);if(it!=memo.end())return it->second;
 int best=0;for(U s=allowed;s;s&=s-1){int x=countr_zero(s);best=max(best,longest(x,U(1)<<x,~allowed));}
 if(memo.size()<2000000)memo[allowed]=best;return best;
}
bool rec(int k,int sum,int x,U m,U ban,int named){
 visits[k]++;int n=popcount(m);if(sum+n+bounds[2-k]+14>=goal){
  masks[k]=m;
  if(k==2){queries++;U free=~(masks[0]|m);
   if(popcount(free)>=goal-sum-n&&maximum(free)+sum+n>=goal){cout<<"FOUND sizes "<<popcount(masks[0])<<" "<<popcount(masks[1])<<" "<<n<<" "<<maximum(free)<<" masks "<<masks[0]<<" "<<masks[1]<<" "<<m<<endl;return true;}
  }else if(rec(k+1,sum+n,x,U(1)<<x,m&~(U(1)<<x),named))return true;
 }
 for(int d=0;d<5&&d<=named;d++){int y=x^(1<<d);if(((ban|m)>>y)&1)continue;
  if(rec(k,sum,y,m|(U(1)<<y),ban|N[x],named+(d==named)))return true;}
 return false;
}
int main(int argc,char**argv){if(argc!=2)return 2;goal=stoi(argv[1]);for(int x=0;x<32;x++)for(int d=0;d<5;d++)N[x]|=U(1)<<(x^(1<<d));
 bool yes=rec(0,0,0,1,0,0);cout<<"DONE target "<<goal<<" attained "<<yes<<" nodes "<<visits[0]<<" "<<visits[1]<<" "<<visits[2]<<" checked "<<queries<<" memo "<<memo.size()<<endl;}
