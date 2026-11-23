#include <algorithm>
#include <array>
#include <bit>
#include <cctype>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;
string canon(const string&s){string a,b;for(int rev=0;rev<2;rev++){int d[9];fill_n(d,9,-1);int n=0;string z;for(int i=0;i<s.size();i++){int x=s[rev?s.size()-1-i:i]-'0';if(d[x]<0)d[x]=n++;z+=char('0'+d[x]);}if(rev)b=z;else a=z;}return min(a,b);}
bool valid(const string&s){array<bool,512> seen{};int v=0;seen[0]=1;for(char c:s){v^=1<<(c-'0');if(seen[v])return false;int count=0;for(int d=0;d<9;d++)count+=seen[v^(1<<d)];if(count!=1)return false;seen[v]=1;}return true;}
set<string> bank[3], stand[3];unordered_map<string,bool>tested;string target;int id=0,lineNum=0;set<pair<int,bool>>matched;set<int> contributors;
void word(const string&s,bool isWhole){
 if(s.size()<189||s.size()>270)return;
 for(int n=189;n<=191;n++)for(int i=0;i+n<=s.size();i++){auto k=canon(s.substr(i,n));bool whole=isWhole&&s.size()==n;
     if(k==target&&matched.emplace(id,whole).second)cout<<"HIT "<<id<<" "<<lineNum<<" "<<whole<<endl;
     auto it=tested.find(k);bool ok=it!=tested.end()?it->second:valid(k);
     if(it==tested.end())tested.emplace(k,ok);if(!ok)continue;
     bank[n-189].insert(k);if(whole)stand[n-189].insert(k);contributors.insert(id);
 }}
void occupancy(const vector<int>&v,int i,int n){
 array<int,512>s{};for(int j=i;j<i+n;j++)if(++s[v[j]]>1)return;
 int tip=-1,ends=0;
 for(int j=i;j<i+n;j++){int x=v[j],d=0;for(int k=0;k<9;k++)d+=s[x^(1<<k)];if(d<1||d>2)return;if(d==1){tip=x;ends++;}}
 if(ends!=2)return;string w;int prev=-1,seen=0;while(tip!=-1){int nxt=-1;for(int k=0;k<9;k++){int x=tip^(1<<k);if(s[x]&&x!=prev){nxt=x;w+=char('0'+k);break;}}seen++;prev=tip;tip=nxt;}
 if(seen==n)word(w,true);
}
void seq(vector<int>&v){
 if(v.size()<189){v.clear();return;}
 string steps,axes;int last=-1234;
 for(int x:v){
  if(x<=8)axes+=char('0'+x);else{word(axes,true);axes.clear();}
  if(last>=0&&has_single_bit(unsigned(last^x)))steps+=char('0'+countr_zero(unsigned(last^x)));else{word(steps,true);steps.clear();}
  last=x;
 }
 word(axes,true);word(steps,true);
 if(v.size()>=190&&v.size()<=196){int st=0;while(st<v.size()){int n=v.size()-st;if(n>=190&&n<=192)occupancy(v,st,n);st++;if(st>4)break;}}
 v.clear();
}
int main(int argc,char**argv){target=argv[1];string l;vector<int>arr;
 while(getline(cin,l)){
  if(l.starts_with("#SRCPATH ")){id=stoi(l.substr(9));lineNum=0;continue;}
  lineNum++;
  if(l.starts_with("10,")||l.starts_with("11,")||l.starts_with("12,")||l.starts_with("13,")){if(l.size()>6&&isdigit(l[3])&&isdigit(l[4])&&isdigit(l[5])&&l[6]==',')continue;}
  for(int i=0;i<l.size();){
    if(isdigit((unsigned char)l[i])){int j=i;while(j<l.size()&&isdigit((unsigned char)l[j]))j++;
      int len=j-i;if(len>=189&&len<=270){bool ok=true;for(int k=i;k<j;k++)ok&=l[k]<='8';
       if(ok)word(l.substr(i,len),true);}
      if(len<=3){int val=0;for(int k=i;k<j;k++)val=val*10+l[k]-48;if(val<=511)arr.push_back(val);else seq(arr);}
      else seq(arr);i=j;
    }else{if(l[i]!=','&&l[i]!=' '&&l[i]!='\t'&&l[i]!='\r')seq(arr);i++;}
  }seq(arr);
 }
 for(int i=0;i<3;i++){ofstream out(string(argv[2])+"/comparison"+to_string(189+i)+".words");for(auto&w:bank[i])out<<w<<'\n';cout<<"COUNT "<<189+i<<" "<<bank[i].size()<<" "<<stand[i].size()<<endl;}
 cout<<"SOURCES";for(auto i:contributors)cout<<" "<<i;cout<<endl;
}
