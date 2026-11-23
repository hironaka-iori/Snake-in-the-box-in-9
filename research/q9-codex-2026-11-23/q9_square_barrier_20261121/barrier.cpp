#define main old_catalogue_driver
#include "../q9_catalogue_tip_core.cpp"
#undef main
#include <random>
#include <unordered_set>
#include <map>
using Pair=pair<int,int>;
struct Middle {
 string word;
 vector<int> p{0};
 array<int,512> ix{},adj{};
 Middle(const string&w):word(w){
  ix.fill(-1);
  for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
  for(int i=0;i<(int)p.size();i++)place(i,p[i]);
 }
 void place(int i,int x){p[i]=x; ix[x]=i;for(int d=0;d<9;d++)adj[x^(1<<d)]++;}
 void flip(int i,int x){int old=p[i];ix[old]=-1;for(int d=0;d<9;d++)adj[old^(1<<d)]--;place(i,x);swap(word[i-1],word[i]);}
 int alt(int i)const{return p[i-1]^p[i]^p[i+1];}
};
struct EndSearch {
 array<int,512> adj{},used{};
 vector<int> left,right,core,bestpath;
 int best,goal=192;uint64_t nodes=0;
 void put(int v,int s){used[v]+=s;for(int d=0;d<9;d++)adj[v^(1<<d)]+=s;}
 bool dfs(int a,int b,bool open,int n){
  nodes++;
  if(n>best){best=n;bestpath.assign(left.rbegin(),left.rend());bestpath.insert(bestpath.end(),core.begin(),core.end());bestpath.insert(bestpath.end(),right.begin(),right.end());}
  if(n==goal)return true;
  if(open&&dfs(a,b,false,n))return true;
  int tip=open?a:b;auto& arm=open?left:right;
  for(int d=0;d<9;d++){int x=tip^(1<<d);if(used[x]||adj[x]!=1)continue;
   put(x,1);arm.push_back(x);if(dfs(open?x:a,open?b:x,open,n+1))return true;arm.pop_back();put(x,-1);
  }
  return false;
 }
 bool run(const string&w,int prior){
  core={0};for(char c:w)core.push_back(core.back()^(1<<(c-'0')));
  for(int v:core)put(v,1);best=prior;return dfs(core.front(),core.back(),true,(int)w.size());
 }
};
using Words=unordered_set<string>;
struct Experiment {
 Words closure,novel;
 vector<const string*> roots;
 size_t attempts=0, barriers=0, restored=0, nodes=0, rootcount=0, depthRec=0;
 array<size_t,16> depths{},maxchords{};
 int best=0, maxnew, deep, samples;
 ofstream traces,records;
 mt19937 gen{2501981};
 Experiment(int trim,int deep_,int m,int n,const string&out):maxnew(m),deep(deep_),samples(n),traces(out+".traces"),records(out+".records"){
  set<string> bank,seeds;
  for(string name:{"comparison189","comparison190","comparison191","outside189"}){
   ifstream in("../q9_far189_spring_20261121/"+name+".words");if(!in)throw runtime_error("no seeds");string w;
   while(in>>w)bank.insert(canonical(w));
  }
  for(auto &w:bank)for(int i=0;i<=trim;i++)seeds.insert(canonical(w.substr(i,w.size()-trim)));
  closure.reserve(trim==24?300000:1400000);for(auto&w:seeds)roots.push_back(&*closure.insert(w).first);
  for(size_t i=0;i<roots.size();i++){
   Middle s(*roots[i]);
   for(int j=1;j+1<int(s.p.size());j++){
    int v=s.alt(j);if(s.ix[v]>=0||s.adj[v]!=2)continue;
    string w=s.word;swap(w[j-1],w[j]);auto t=closure.insert(canonical(w));if(t.second)roots.push_back(&*t.first);
   }
  }
  cout<<"CLOSURE "<<bank.size()<<" "<<seeds.size()<<" "<<roots.size()<<endl;
  if(trim==24&&roots.size()!=250346)throw runtime_error("mismatch in closure24");
  if(trim==36&&roots.size()!=1265614)throw runtime_error("mismatch in closure36");
  shuffle(roots.begin(),roots.end(),gen);
 }
 bool hit(const string&origin,const string&raw,const vector<int>&moves,int peak){
  restored++;string w=canonical(raw);if(closure.count(w)||!novel.insert(w).second)return false;
  depths.at(moves.size())++;maxchords.at(peak)++;
  traces<<origin<<" "<<w<<" "<<peak;for(int i:moves)traces<<" "<<i;traces<<"\n";
  EndSearch es;bool found=es.run(w,best);nodes+=es.nodes;
  if(es.best>best){best=es.best;string pw;
   for(int i=1;i<(int)es.bestpath.size();i++)pw+=char('0'+countr_zero(unsigned(es.bestpath[i]^es.bestpath[i-1])));
   cout<<"BEST "<<best<<" "<<novel.size()<<endl;records<<best<<" "<<w<<" "<<pw<<endl;
  }
  if(found)cout<<"FOUND192 "<<w<<endl;
  return found||novel.size()>=size_t(maxnew);
 }
 bool step(const string&origin,Middle&s,vector<Pair>&bad,vector<int>&moves,int peak,int limit){
  vector<int> positions;
  if(bad.empty()){for(int j=1;j+1<int(s.p.size());j++)positions.push_back(j);}
  else if(moves.size()+1==size_t(limit)){
   for(int j:{bad[0].first,bad[0].second})if(all_of(bad.begin(),bad.end(),[&](Pair ab){return ab.first==j||ab.second==j;}))positions.push_back(j);
  }else{
   for(auto [a,b]:bad)for(int z:{a,b})for(int t=z-1;t<=z+1;t++)positions.push_back(t);
   sort(positions.begin(),positions.end());positions.erase(unique(positions.begin(),positions.end()),positions.end());
  }
  for(int j:positions){
   if(j<=0||j+1>=int(s.p.size())||(!moves.empty()&&j==moves.back()))continue;
   int old=s.p[j],v=s.alt(j);if(s.ix[v]>=0)continue;
   int rem=0;for(auto [a,b]:bad)rem+=a!=j&&b!=j;
   int how=rem+s.adj[v]-2;
   if(how>2||(moves.empty()&&how==0)||(moves.size()+1==size_t(limit)&&how!=0))continue;
   attempts++;vector<Pair> nb;
   for(auto ab:bad)if(ab.first!=j&&ab.second!=j)nb.push_back(ab);
   for(int d=0;d<9;d++){int k=s.ix[v^(1<<d)];if(k>=0&&abs(k-j)>1)nb.push_back({j,k});}
   if(nb.size()!=size_t(how))throw runtime_error("bad count");
   if(moves.empty())barriers++;
   s.flip(j,v);moves.push_back(j);
   bool stop=nb.empty()?hit(origin,s.word,moves,peak):step(origin,s,nb,moves,max(peak,how),limit);
   moves.pop_back();s.flip(j,old);if(stop)return true;
  }
  return false;
 }
 void run(){
  vector<Pair> bad;vector<int> moves;
  for(auto root:roots){Middle s(*root);rootcount++;
   if(step(*root,s,bad,moves,0,deep)||rootcount>=size_t(samples))break;
  }
  cout<<"DONE roots "<<rootcount<<" visited_flips "<<attempts<<" first_illegal "<<barriers<<" legal_returns "<<restored<<" outside "<<novel.size()<<" nodes "<<nodes<<" max "<<best<<endl;
  for(int i=0;i<16;i++)if(depths[i])cout<<"DEPTH "<<i<<" "<<depths[i]<<endl;
  for(int i=0;i<16;i++)if(maxchords[i])cout<<"PEAK "<<i<<" "<<maxchords[i]<<endl;
 }
};
#ifndef BARRIER_LIBRARY
int main(int argc,char**argv){if(argc!=6)return 2;Experiment ex(stoi(argv[1]),stoi(argv[2]),stoi(argv[3]),stoi(argv[4]),argv[5]);ex.run();}

#endif
