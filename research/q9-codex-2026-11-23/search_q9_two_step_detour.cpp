// Replace m consecutive 190-snake vertices with m+2, collecting one-chord 192 walks.
#define Q9_FIXED_BRIDGE_NO_DRIVER
#include "search_q9_fixed_bridge.cpp"
#undef Q9_FIXED_BRIDGE_NO_DRIVER
struct Detour{
 Walk w;int left,right,remaining,cap,nodes=0,limit,kept=0;
 mt19937 &g;unordered_set<string>&classes;ostream&output;vector<int> add;
 Detour(vector<int>p,int l,int m,int cap_,int lim,mt19937 &gen,unordered_set<string>&bank,ostream&out):
  w(9,p),left(l),right(l+m),remaining(m+2),cap(cap_),limit(lim),g(gen),classes(bank),output(out){}
 bool dfs(int x,int n,int budget){
  if(++nodes>cap)return false;
  if(!n){
   vector<int> p(w.p.begin(),w.p.begin()+left);
   p.insert(p.end(),add.begin(),add.end());p.insert(p.end(),w.p.begin()+right,w.p.end());
   int cost=limit-budget;
   if(!cost){
    Walk check(9,p);check.verify();if(check.E)abort();
    cout<<"FOUND";for(int a:p)cout<<" "<<a;cout<<endl;return true;
   }
   if(classes.insert(key(p)).second){
    Walk check(9,p);check.verify();if(check.E!=cost)abort();
    for(size_t i=0;i<p.size();i++)output<<(i?" ":"")<<p[i];output<<endl;kept++;
   }
   return false;
  }
  int b=right==(int)w.p.size()?-1:w.p[right];
  array<pair<unsigned,int>,9> opt;int k=0;
  for(int d=0;d<9;d++){
   int v=x^(1<<d);if(w.cnt[v])continue;
   if(b>=0){int h=popcount((unsigned)(v^b));if(h>n||(n==1&&h!=1))continue;}
   int delta=w.near[v]-1-(b>=0&&n==1);
   if(delta<=budget)opt[k++]={unsigned(g()%32+delta*27),v};
  }
  sort(opt.begin(),opt.begin()+k);
  for(int i=0;i<k&&nodes<cap&&kept<2;i++){
   int v=opt[i].second;int delta=w.near[v]-1-(b>=0&&n==1);
   w.edit(v,1);add.push_back(v);
   if(dfs(v,n-1,budget-delta))return true;
   add.pop_back();w.edit(v,-1);
  }
  return false;
 }
 bool run(){
  for(int i=left;i<right;i++)w.edit(w.p[i],-1);
  int cost=w.E+right-left+(right<(int)w.p.size());
  return cost<=limit&&dfs(w.p[left-1],remaining,limit-cost);
 }
};
int main(int argc,char**argv){
 if(argc!=7&&argc!=8)return 2;
 int limit=argc==8?stoi(argv[7]):1;
 int width=stoi(argv[1]),stride=stoi(argv[2]),cap=stoi(argv[3]),target=stoi(argv[4]);
 mt19937 gen(stoi(argv[5]));ofstream out(argv[6]);if(!out)return 3;
 string line;unordered_set<string> bank;int row=0;long long cases=0,nodes=0,capped=0;
 while(getline(cin,line)){
  istringstream in(line);vector<int> p;int v;while(in>>v)p.push_back(v);if(p.empty())continue;
  Walk check(9,p);check.verify();if(check.E)return 4;
  if((int)p.size()>target-1)p.resize(target-1);
  if((int)p.size()!=target-1)return 5;
  vector<int> starts;for(int i=1+row%stride;i+width<=(int)p.size();i+=stride)starts.push_back(i);
  starts.push_back(p.size()-width);sort(starts.begin(),starts.end());starts.erase(unique(starts.begin(),starts.end()),starts.end());
  for(int l:starts){
   Detour t(p,l,width,cap,limit,gen,bank,out);if(t.run())return 0;
   nodes+=t.nodes;capped+=(t.nodes>=cap);cases++;
  }
  reverse(p.begin(),p.end());Detour t(p,p.size()-width,width,cap,limit,gen,bank,out);if(t.run())return 0;
  cases++;nodes+=t.nodes;capped+=t.nodes>=cap;
  if(++row%100==0)cout<<"CHECK "<<row<<" cases "<<cases<<" nodes "<<nodes<<" cap "<<capped<<" distinct "<<bank.size()<<endl;
 }
 cout<<"DONE "<<row<<" cases "<<cases<<" nodes "<<nodes<<" cap "<<capped<<" distinct "<<bank.size()<<endl;
}
