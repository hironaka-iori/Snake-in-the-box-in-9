#include <algorithm>
#include <array>
#include <bitset>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Pattern{vector<vector<int>> groups;};
bool place(array<int,8>& allowed,int k,int used){if(!k)return true;int choices=allowed[k-1]&~used;while(choices){int v=choices&-choices;if(place(allowed,k-1,used|v))return true;choices^=v;}return false;}
int main(){
 ifstream f("../q8_catalogue_96_98.words"),d("../q9_gap_generations/prior191.words");string w;set<string> seen;
 while(f>>w){for(int rep=0;rep<2;rep++){for(int i=0;i+25<=(int)w.size();i++){string s=w.substr(i,25);array<char,8> labels{};int next=0;for(char &c:s){auto &id=labels[c-'0'];if(!id)id=char('A'+next++);c=id;}seen.insert(s);}reverse(w.begin(),w.end());}}
 vector<Pattern> patterns;
 for(auto &s:seen){array<vector<int>,8> uses;for(int i=0;i<25;i++)uses[s[i]-'A'].push_back(i);sort(uses.begin(),uses.end(),[](auto&a,auto&b){return a.size()>b.size();});Pattern p;for(auto &g:uses)if(g.size())p.groups.push_back(g);patterns.push_back(p);}
 long long checks=0,nonempty=0,hits=0,starts=0;
 while(d>>w)for(int off=0;off+50<=(int)w.size();off++){++starts;array<int,25> pa;for(int j=0;j<25;j++)pa[j]=(1<<(w[off+2*j]-'0'))|(1<<(w[off+2*j+1]-'0'));
 for(auto &p:patterns){++checks;array<int,8> domains;int k=0;
 for(auto &g:p.groups){int allowed=511;for(int t:g)if(!(allowed&=pa[t]))break;if(!allowed)break;domains[k++]=allowed;}
 if(k==(int)p.groups.size()){++nonempty;hits+=place(domains,k,0);}
 }}
 cout<<"length_25_patterns "<<patterns.size()<<" starts "<<starts<<" tested "<<checks<<" nonempty_domains "<<nonempty<<" injective_placements "<<hits<<endl;
}
