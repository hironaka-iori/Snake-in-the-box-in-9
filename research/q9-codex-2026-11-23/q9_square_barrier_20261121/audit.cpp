#include <algorithm>
#include <cassert>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Set=unordered_set<string>;
string one(const string&w){string k;array<char,9> ren{};char c='0';for(char x:w){char &label=ren.at(x-'0');if(!label)label=c++;k+=label;}return k;}
string key(const string&w){return min(one(w),one(string(w.rbegin(),w.rend())));}
vector<int> path(const string&w){vector<int>v{0};for(char d:w)v.push_back(v.back()^(1<<(d-'0')));return v;}
bool induced(const vector<int>&p){
 for(int i=0;i<(int)p.size();i++)for(int j=0;j<i;j++){int h=popcount(unsigned(p[i]^p[j]));if(h==0||(h==1)!=(j+1==i))return false;}return true;
}
void close(Set&allowed,vector<const string*>&q){
 for(size_t i=0;i<q.size();i++){const string&w=*q[i];auto v=path(w);array<bool,512>occupied{};for(int x:v)occupied[x]=true;
  for(int j=1;j+1<(int)v.size();j++){
   int x=v[j-1]^(v[j+1]^v[j]);if(occupied[x])continue;
   bool valid=true;for(int d=0;d<9;d++){int n=x^(1<<d);if(n!=v[j-1]&&n!=v[j+1]&&occupied[n]){valid=false;break;}}
   if(valid){string t=w;swap(t[j-1],t[j]);auto a=allowed.insert(key(t));if(a.second)q.push_back(&*a.first);}
  }
 }
}
int main(int argc,char**argv){
 if(argc<4)return 2;int trim=stoi(argv[1]);Set allowed,bank;vector<const string*> q;
 for(string name:{"comparison189","comparison190","comparison191","outside189"}){ifstream f("../q9_far189_spring_20261121/"+name+".words");assert(f);string w;while(f>>w){assert(induced(path(w)));bank.insert(key(w));}}
 for(const auto&w:bank)for(int i=0;i<=trim;i++){auto it=allowed.insert(key(w.substr(i,w.size()-trim)));if(it.second)q.push_back(&*it.first);}
 close(allowed,q);cout<<"CATALOGUE_CLOSURE "<<allowed.size()<<endl;set<string> known190,known191;
 for(const string&w:bank)if(w.size()==190)known190.insert(w);else if(w.size()==191)known191.insert(w);
 if(string(argv[2])!="-"){
  q.clear();ifstream seeds(argv[2]);assert(seeds);string line;while(getline(seeds,line)){istringstream ss(line);string a,b;ss>>a>>b;auto it=allowed.insert(b);if(it.second)q.push_back(&*it.first);}
  close(allowed,q);cout<<"WITH_FIRST_CROSSINGS "<<allowed.size()<<endl;
 }
 for(int f=3;f<argc;f++){
  string base=argv[f],line;ifstream traces(base+".traces");Set seen;long long intermediate=0,full=0;
  if(traces)while(getline(traces,line)){istringstream ss(line);string w,end;int peak;ss>>w>>end>>peak;
   assert(allowed.count(w)&&!allowed.count(end)&&seen.insert(end).second);
   auto p=path(w);int j,observed=0,chords=0;bool checkfull=seen.size()%509==1;
   while(ss>>j){
    assert(j>0&&j+1<(int)p.size());int old=p[j];swap(w[j-1],w[j]);int x=p[j-1]^(1<<(w[j-1]-'0'));
    assert(x!=old&&popcount(unsigned(x^p[j+1]))==1);
    for(int k=0;k<(int)p.size();k++)if(k!=j){assert(p[k]!=x);if(abs(j-k)>1)chords+=(popcount(unsigned(x^p[k]))==1)-(popcount(unsigned(old^p[k]))==1);}
    p[j]=x;if(checkfull){int brute=0;for(int i=0;i<(int)p.size();i++)for(int k=0;k+1<i;k++)brute+=popcount(unsigned(p[i]^p[k]))==1;assert(brute==chords);full++;}
    assert(0<=chords&&chords<=2);if(chords)intermediate++;observed=max(observed,chords);
   }
   assert(observed==peak&&peak>=1&&chords==0&&key(w)==end);
  }
  ifstream rec(base+".records");assert(rec);int n,best=0;string core,pw,last;
  while(rec>>n>>core>>pw){assert((int)pw.size()==n&&induced(path(pw))&&pw.find(core)!=string::npos);best=max(n,best);last=key(pw);}
  cout<<base<<" unique_traces "<<seen.size()<<" illegal_stages "<<intermediate<<" pairwise_intermediate_checks "<<full<<" best "<<best<<" best_in_same_length_bank "<<(best==190?known190.count(last):best==191?known191.count(last):0)<<endl;
 }
}
