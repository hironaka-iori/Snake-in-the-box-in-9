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
 string w;unordered_set<string> kn;long long cap=0;while(cin>>w){if((int)w.size()<(target-1+1)/2)continue;Ax a{};auto r=norm(rev(w),a);for(auto b:vector<string>{w,r}){for(auto C:near(b,0,target-1-b.size())){if(C.w.size()>b.size())continue;string full=rev(b)+"6"+C.w;if(!valid(full))abort();cap++;string key=canon(full);if(kn.insert(key).second)cout<<key<<endl;}}}cerr<<"placements before orbit classification "<<cap<<" Q7 donors "<<kn.size()<<endl;}