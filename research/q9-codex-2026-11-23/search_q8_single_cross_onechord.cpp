// Two true Q8 snakes are rooted at twin vertices. Every other overlap gives
// precisely one chord of the resulting Q9 walk.
#define main previous_bank_join
#include "search_q8_bank_join.cpp"
#undef main
#include <unordered_set>
#include <numeric>
using namespace std;
string canonical(const vector<int>&p){
 string best;
 for(int dir:{1,-1}){
  int first=dir==1?0:p.size()-1;array<int,9>labels;labels.fill(-1);string code;int n=0;
  for(int step=1;step<(int)p.size();step++){
   int i=first+dir*(step-1),d=countr_zero((unsigned)(p[i]^p[i+dir]));
   if(labels[d]<0)labels[d]=n++;
   code.push_back(char(labels[d]));
  }
  if(best.empty()||code<best)best=code;
 }
 return best;
}
int main(int argc,char**argv){
 if(argc<5)return 2;int target=stoi(argv[1]),budget=stoi(argv[2]);ofstream out(argv[3]);if(!out)return 3;
 array<vector<Arm>,101>bysize;set<string>forms;
 for(int fi=4;fi<argc;fi++){ifstream in(argv[fi]);if(!in)return 4;string word;while(in>>word){
  if(word.size()>100||!forms.insert(word).second)continue;
  Arm a;a.vertices.push_back(0);for(char d:word){if(d<'0'||d>'7')return 5;int v=a.vertices.back()^(1<<(d-'0'));a.vertices.push_back(v);mark(a.mask,v);}
  for(int i=0;i<(int)a.vertices.size();i++)for(int j=0;j<i;j++){int e=popcount((unsigned)(a.vertices[i]^a.vertices[j]));if(!e||(e==1)!=(i==j+1))return 6;}
  bysize[word.size()].push_back(a);
 }}
 unordered_set<string>classes;uint64_t tested=0,hits=0;
 for(int len=100;len>=0;len--){
  int mate=target-1-len;if(mate<0||mate>len||bysize[len].empty()||bysize[mate].empty())continue;
  const auto&needle=bysize[len];const auto&hay=bysize[mate];
  array<int,8>perm; iota(perm.begin(),perm.end(),0);uint64_t pairs=uint64_t(needle.size())*hay.size()*40320;
  int minimum=257;uint64_t best_count=0;vector<int> best_path;
  do{
   array<int,256>image{};for(int v=1;v<256;v++)image[v]=image[v&(v-1)]|(1<<perm[countr_zero((unsigned)v)]);
   for(auto&b:needle){
    Mask m{};for(int i=1;i<(int)b.vertices.size();i++)mark(m,image[b.vertices[i]]);
    for(auto&a:hay){
     int c=0;
     for(int k=0;k<4;k++){c+=popcount(m[k]&a.mask[k]);if(c>max(budget,minimum))break;}
     if(c<=minimum){
      if(c<minimum){
       minimum=c;best_count=0;best_path.assign(a.vertices.rbegin(),a.vertices.rend());
       for(int v:b.vertices)best_path.push_back(256+image[v]);
      }
      best_count++;
     }
     if(c>budget)continue;
     hits++;
     vector<int>p(a.vertices.rbegin(),a.vertices.rend());for(int v:b.vertices)p.push_back(256+image[v]);
     if(!c){cout<<"FOUND";for(int v:p)cout<<" "<<v;cout<<endl;return 0;}
     if(classes.insert(canonical(p)).second){for(int i=0;i<(int)p.size();i++)out<<(i?" ":"")<<p[i];out<<endl;}
    }
   }
  }while(next_permutation(perm.begin(),perm.end()));
  cout<<"MIN "<<len<<" "<<mate<<" "<<minimum<<" count "<<best_count<<" sample";for(int v:best_path)cout<<" "<<v;cout<<endl;
  tested+=pairs;cout<<"CHECK "<<len<<" "<<mate<<" placements "<<tested<<" low_hit "<<hits<<" unique "<<classes.size()<<endl;
 }
 cout<<"DONE "<<target<<" placements "<<tested<<" low_hit "<<hits<<" unique "<<classes.size()<<endl;
}
