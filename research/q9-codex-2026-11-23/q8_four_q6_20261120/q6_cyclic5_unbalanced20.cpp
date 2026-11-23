#include <algorithm>
#include <bit>
#include <iostream>
#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <array>
#include <string>
using namespace std;using U=uint64_t;
U adj[64],m[6];unsigned char cap[65536];
U nb(U x){U a=0;for(int i=0;i<6;i++){int z=1<<i;a|=((x&m[i])<<z)|((x&~m[i])>>z);}return a;}
int bound(U x){return cap[uint16_t(x)]+cap[uint16_t(x>>16)]+cap[uint16_t(x>>32)]+cap[uint16_t(x>>48)];}
using Ax=array<int,8>;
string norm(string s,Ax& inv){Ax map;map.fill(-1);int k=0;for(char& c:s){int i=c-'0';if(map[i]<0){map[i]=k;inv[k++]=i;}c='0'+map[i];}return s;}
string canon(string s){Ax a;auto t=norm(s,a);reverse(s.begin(),s.end());return min(t,norm(s,a));}
struct Arm{string w;U mask;int last;};
Arm readarm(string w,int root=0){int x=root;U mask=1ull<<x;for(char c:w){x^=1<<(c-'0');mask|=1ull<<x;}return {w,mask,x};}
unordered_map<string,vector<string>> cache;int floorL;long long dfsnodes=0,hits=0,mid=0,checks=0,shapes=0,newsh=0;
const vector<string>& opts(const string& word,int goal){auto cachekey=char(goal)+word;auto it=cache.find(cachekey);if(it!=cache.end())return it->second;
 auto aa=readarm(word);vector<string> dst;string p;
 auto walk=[&](auto&&self,int x,U free)->void{dfsnodes++;int n=p.size();if(n>=goal)dst.push_back(p);U cc=1ull<<x;while(1){U d=nb(cc)&free&~cc;if(!d)break;cc|=d;}
 if(bound(cc)<max(goal,n+1)-n+1)return;
 U cand=cc&adj[x],base=cc&~(cand|(1ull<<x));while(cand){int y=countr_zero(cand);cand&=cand-1;p+='0'+countr_zero(unsigned(x^y));self(self,y,base|(1ull<<y));p.pop_back();}};
 walk(walk,0,~aa.mask|1ull);return cache.emplace(cachekey,move(dst)).first->second;}
vector<Arm> near(const string& word,int root,int goal){Ax a{};auto key=norm(word,a);vector<Arm> out;for(string s:opts(key,goal)){for(char&c:s)c='0'+a[c-'0'];out.push_back(readarm(s,root));}return out;}
string rev(string s){reverse(s.begin(),s.end());return s;}
bool valid(const string&w){int x=0;vector<int> pts{0};for(char c:w){x^=1<<(c-'0');for(int i=0;i+1<(int)pts.size();i++)if(popcount(unsigned(pts[i]^x))<=1)return false;pts.push_back(x);}return true;}
int main(int argc,char**argv){floorL=stoi(argv[1]);int target=stoi(argv[2]),start=stoi(argv[3]),end=stoi(argv[4]);for(int x=0;x<64;x++)for(int i=0;i<6;i++){adj[x]|=1ull<<(x^1<<i);if(!(x>>i&1))m[i]|=1ull<<x;}
 for(int a=1;a<65536;a++){bool ok=true;int ends=0;for(int x=0;x<16;x++)if(a>>x&1){int k=popcount(adj[x]&a);ok&=k<=2;if(k<2)ends|=1<<x;}int comp=ends;while(ok){int t=nb(comp)&a;if(!(t&~comp))break;comp|=t;}if(ok&&a==comp)cap[a]=popcount(unsigned(a));else for(int s=a;s;s&=s-1)cap[a]=max(cap[a],cap[a&~(s&-s)]);}

 string w;unordered_set<string> known;for(int z=5;z<argc;z++){ifstream f(argv[z]);while(f>>w)if((int)w.size()>=target)known.insert(canon(w));}unordered_set<string> found;int row=0;long long pairs=0,ruled=0,boundok=0,walks=0,ends=0;
 while(cin>>w){if((int)w.size()<floorL)continue;if(row>=end)break;if(row++<start)continue;
 auto C=readarm(w);int c=w.size(),bmin=max(floorL,target-4-49-c);
 auto ls=near(w,0,bmin);auto rs=near(rev(w),C.last,bmin);
 array<vector<Arm>,27> LL,RR;for(auto&a:ls)LL[a.w.size()].push_back(move(a));for(auto&a:rs)RR[a.w.size()].push_back(move(a));
 
 for(int b=bmin;b<=26;b++)for(int d=bmin;d<=26;d++){
 int needW=target-4-b-c-d;
 if(needW>min({26,49-b,49-d}) || (min({b,c,d})>=21))continue;
 for(auto&B:LL[b])for(auto&D:RR[d]){pairs++;int x=B.last,y=D.last;U X=1ull<<x,Y=1ull<<y;
 if((X&D.mask)||(Y&B.mask)||(adj[x]&Y))continue;ruled++;
 U space=~(B.mask|D.mask)|X|Y;int required=target-2-(int)(w.size()+B.w.size()+D.w.size());
 if(bound(space)<required)continue;
 boundok++;string left,right;
 auto component=[](U seeds,U free){U reach=seeds;while(1){U newbits=nb(reach)&free&~reach;if(!newbits)return reach;reach|=newbits;}};
 auto rr=[&](auto&&self,int z,U room)->void{walks++;int n=(int)(left.size()+right.size())+2;U Z=1ull<<z;
 if(n>=required){string full=rev(left)+"6"+rev(B.w)+"7"+w+"6"+D.w+"7"+right;if(!valid(full))abort();full=canon(full);if(found.insert(full).second&&!known.count(full))cout<<full<<endl;++ends;}
 U reach=component(Z,room);if(n-1+bound(reach)<max(n+1,required))return;
 U cand=adj[z]&room,rest=room&~(adj[z]|Z);while(cand){int v=countr_zero(cand);cand&=cand-1;right+='0'+countr_zero(unsigned(v^z));self(self,v,rest|(1ull<<v));right.pop_back();}};
 auto ll=[&](auto&&self,int z,U room)->void{walks++;U Z=1ull<<z;
 if((int)left.size()+bound(component(Z|Y,room))<required)return;
 U rest=room&~(adj[z]|Z);if((int)left.size()+1+bound(component(Y,rest))>=required)rr(rr,y,rest);
 U cand=adj[z]&room&~(Y|adj[y]);while(cand){int v=countr_zero(cand);cand&=cand-1;left+='0'+countr_zero(unsigned(v^z));self(self,v,rest|(1ull<<v));left.pop_back();}};
 ll(ll,x,space);}
 }
 if(row%100==0)cerr<<"row "<<row<<" pairs "<<pairs<<" compatible "<<ruled<<" forestcap "<<boundok<<" dfs "<<walks<<" hits "<<ends<<" shapes "<<found.size()<<endl;
 }cerr<<"final row "<<row<<" pairs "<<pairs<<" compatible "<<ruled<<" forestcap "<<boundok<<" dfs "<<walks<<" hits "<<ends<<" shapes "<<found.size()<<endl;}
