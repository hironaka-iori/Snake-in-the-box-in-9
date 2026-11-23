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
 string w;unordered_set<string> known,occ;for(int z=5;z<argc;z++){ifstream f(argv[z]);while(f>>w){if(w.size()>=size_t(target))known.insert(canon(w));}}
 int rows=0;while(cin>>w){if((int)w.size()<(target-3-52+1)/2)continue;if(rows>=end)break;if(rows++<start)continue;Ax ax{};vector<string> dirs{w};string reverseword=norm(rev(w),ax);if(w!=reverseword)dirs.push_back(reverseword);
 for(auto b:dirs){auto B=readarm(b);int ub=49, armub=26, bL=b.size(), need=target-3;auto left=near(rev(b),B.last,max({floorL,need-bL-ub,need-bL-min(bL,armub)-armub}));
 if(left.empty())continue;int leftmax=0;for(auto&a:left)leftmax=max(leftmax,(int)a.w.size());auto middle=near(b,0,max(floorL,need-bL-leftmax-armub));
 for(auto& C:middle){mid++;int cLen=C.w.size(),bLen=b.size();if(cLen>bLen||need-bLen-cLen-leftmax>armub)continue;auto right=near(rev(C.w),C.last,max(floorL,need-bLen-cLen-leftmax));
 for(auto& A:left)for(auto& D:right){if((int)(A.w.size()+D.w.size())+bLen+cLen+3<target)continue;checks++;if(A.mask&D.mask)continue;hits++;
 string s=rev(A.w)+"6"+rev(b)+"7"+C.w+"6"+D.w;if(!valid(s)){cerr<<"invalid"<<endl;abort();}s=canon(s);if(!occ.insert(s).second)continue;shapes++;if(!known.count(s)){newsh++;cout<<s<<endl;}}
 }}
 if(rows%1000==0)cerr<<"tick "<<rows<<" mid "<<mid<<" checks "<<checks<<" hits "<<hits<<" shapes "<<shapes<<" new "<<newsh<<" cache "<<cache.size()<<endl;}
 cerr<<"final rows "<<rows<<" dfscalls "<<dfsnodes<<" mid "<<mid<<" checks "<<checks<<" hits "<<hits<<" shapes "<<shapes<<" new "<<newsh<<" cache "<<cache.size()<<endl;}
