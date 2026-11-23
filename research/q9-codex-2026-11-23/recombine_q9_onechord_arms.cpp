// Exchange large rooted arms between donors with a matching initial hinge pattern.
#define Q9_PERM_CLOSURE_NO_MAIN
#include "search_q9_onechord_perm_closure.cpp"
#include <unordered_map>
string rooted(const vector<int>&p){
 array<int,9>labels;labels.fill(-1);int n=0;string s;
 for(int i=1;i<(int)p.size();i++){
  int a=countr_zero((unsigned)(p[i]^p[i-1]));if(labels[a]<0)labels[a]=n++;
  s.push_back(char(labels[a]));
 }return s;
}
vector<vector<int>> load(const char*file){
 ifstream in(file);if(!in)abort();vector<vector<int>>rows;string line;
 while(getline(in,line)){istringstream stream(line);vector<int>q;int v;while(stream>>v)q.push_back(v);if(q.empty())continue;Walk t(9,q);t.verify();if(t.E>1)abort();rows.push_back(q);}
 return rows;
}
int main(int argc,char**argv){
 if(argc!=8)return 2;auto parents=load(argv[1]);auto donors=load(argv[2]);Bank bank(argv[7]);
 if(!bank.out)return 3;
 int left=stoi(argv[3]),right=192-left,hinge=stoi(argv[4]),stop=stoi(argv[5]);mt19937 gen(stoi(argv[6]));
 unordered_map<string,vector<int>>choices;unordered_map<string,vector<string>> groups;
 for(auto p:donors){
  for(int dir=0;dir<2;dir++,reverse(p.begin(),p.end())){
   for(int j=0;j+right<(int)p.size();j++){
    vector<int>q(p.begin()+j,p.begin()+j+right+1);
    string code=rooted(q);
    if(choices.emplace(code,q).second)groups[code.substr(0,hinge)].push_back(code);
   }
  }
 }
 for(auto&[_,items]:groups)shuffle(items.begin(),items.end(),gen);
 unordered_set<string>seen;long long pairs=0,compatible=0,anchors=0;
 for(auto p:parents)for(int dir=0;dir<2;dir++,reverse(p.begin(),p.end())){
  if((int)p.size()!=193)return 4;vector<int>a(p.begin(),p.begin()+left+1),orig(p.begin()+left,p.end());
  Walk ta(9,a),tb(9,orig);if(ta.E||tb.E)continue;anchors++;
  string sa=rooted(a),sb=rooted(orig),grp=sb.substr(0,hinge);
  auto it=groups.find(grp);if(it==groups.end())continue;int tried=0;
  for(auto&other:it->second){
   if(other==sb)continue;
   string k=sa+other;if(!seen.insert(k).second)continue;
   auto&q=choices.at(other);vector<int>w=a;for(int j=1;j<=right;j++)w.push_back(q[j]^q[0]^a.back());
   auto before=bank.leaves;Permute engine(w,left,0,bank);pairs++;
   if(engine.visit(0,511,0))return 0;
   compatible+=bank.leaves>before;
   if(++tried>=stop)break;
  }
 }
 cout<<"DONE anchors "<<anchors<<" donor_arms "<<choices.size()<<" distinct_pairs "<<pairs<<" compatible "<<compatible
     <<" near_classes "<<bank.seen.size()<<" nodes "<<bank.nodes<<" leaves "<<bank.leaves<<endl;
}
